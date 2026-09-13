#!/usr/bin/env python3
"""GPL-2.0-or-later. Source-AST to actual WASM translation validation.

All positive equivalence obligations must be UNSAT in both Z3 and cvc5.
Unsupported source/target semantics, solver unknown, timeout, or missing shipped
functions fail the command. Extraction, parsing, and the two interpreters remain
in the trusted base. No universal claim about Clang, LLVM, or Binaryen follows.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import time
import z3
import cvc5
from model import Source, Unsupported, initial_state, function_nodes, F64, ZERO
from wasm import Module, Machine, Instruction

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]


def sha(data): return hashlib.sha256(data).hexdigest()

def run(command,env):
    result=subprocess.run([str(x) for x in command],cwd=ROOT,env=env,text=True,capture_output=True,timeout=180)
    if result.returncode:raise RuntimeError(result.stderr+result.stdout)
    return result.stdout


def extract(text,name):
    matches=list(re.finditer(rf'(?:^|\n)(?:double|void) DLL_FUNC {re.escape(name)}\([^;{{}}]*\)\s*\{{',text))
    if len(matches)!=1:raise Unsupported('Expected one actual source definition '+name)
    start,end=matches[0].start(),matches[0].end();depth=1
    while depth and end<len(text):
        depth+=(text[end]=='{')-(text[end]=='}');end+=1
    if depth:raise Unsupported('Unterminated definition')
    return text[start:end].strip()


def slim(node):
    keep={'kind','name','type','value','opcode','castKind','referencedDecl','inner','valueCategory','init','isPostfix'}
    return {k:([slim(x) for x in v] if k=='inner' else slim(v) if isinstance(v,dict) and k=='referencedDecl' else v)
            for k,v in node.items() if k in keep}


def replay_cvc(smt):
    solver=cvc5.Solver();solver.setOption('tlimit-per','30000')
    parser=cvc5.InputParser(solver)
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6,'(set-logic ALL)\n'+smt,'obligation')
    responses=[]
    while True:
        command=parser.nextCommand()
        if command.isNull():break
        result=command.invoke(solver,parser.getSymbolManager()).strip()
        if result:responses.append(result)
    if len(responses)!=1 or responses[0] not in {'sat','unsat','unknown'}:
        raise RuntimeError('Unexpected cvc5 result '+repr(responses))
    return responses[0]


class Obligations:
    def __init__(self,out):self.out=out;self.records=[];out.mkdir(parents=True,exist_ok=True)
    def check(self,name,formula,expected='unsat',metadata=None):
        solver=z3.Solver();solver.set(timeout=30000);solver.add(formula)
        smt=solver.to_smt2();path=self.out/(name+'.smt2');path.write_text(smt)
        start=time.monotonic();result=str(solver.check());z3_seconds=time.monotonic()-start
        if result!=expected:raise AssertionError(f'{name}: Z3 {result}, expected {expected}')
        start=time.monotonic();independent=replay_cvc(smt);cvc_seconds=time.monotonic()-start
        if independent!=expected:raise AssertionError(f'{name}: cvc5 {independent}, expected {expected}')
        record={'name':name,'z3':result,'cvc5':independent,'z3Seconds':z3_seconds,'cvc5Seconds':cvc_seconds,
                'smt2SHA256':sha(smt.encode()),**(metadata or {})}
        self.records.append(record);print(f'{name}: {result} / {independent}',flush=True)
        return record


def sqrt_zero_rewrite(expr):
    """Instantiate only the separately discharged forall-f64 sqrt-zero lemma.

    No algebraic reassociation, real-number approximation, or unchecked optimizer
    rewrite is performed here. The FP theory identifies NaNs but distinguishes
    signed zeros; fp.eq, unlike '=', treats both zeros as equal.
    """
    changes=[]
    def walk(node):
        if not z3.is_app(node):return
        if node.decl().kind()==z3.Z3_OP_FPA_EQ:
            left,right=node.children()
            for value,other in [(left,right),(right,left)]:
                if z3.is_app(value) and value.decl().kind()==z3.Z3_OP_FPA_SQRT and z3.is_true(z3.simplify(z3.fpEQ(other,ZERO))):
                    changes.append((node,z3.fpEQ(value.arg(1),ZERO)))
        for child in node.children():walk(child)
    walk(expr)
    return z3.substitute(expr,*changes) if changes else expr


def congruence_abstraction(expr):
    """Sound overapproximation, never an assumed arithmetic identity.

    Replace each distinct unchanged FP arithmetic term by one arbitrary FP
    value. Identical terms share a symbol; different terms remain unrelated.
    Every concrete IEEE valuation is an instance of this stronger model.
    The exact round-trip assertion guards the substitution implementation.
    """
    arithmetic={z3.Z3_OP_FPA_ADD,z3.Z3_OP_FPA_SUB,z3.Z3_OP_FPA_MUL,z3.Z3_OP_FPA_DIV,z3.Z3_OP_FPA_SQRT}
    terms={}
    def visit(node):
        if z3.is_app(node) and node.decl().kind() in arithmetic:
            if node.get_id() not in terms:
                terms[node.get_id()]=(node,z3.FP('arithmetic_'+str(len(terms)),F64))
        for child in node.children():visit(child)
    visit(expr)
    pairs=list(terms.values())
    abstract=z3.substitute(expr,*pairs) if pairs else expr
    restored=z3.substitute(abstract,*[(symbol,original) for original,symbol in pairs]) if pairs else abstract
    if not restored.eq(expr):raise AssertionError('Abstraction round-trip failed')
    return abstract,[{'symbol':str(symbol),'originalSMT':original.sexpr()} for original,symbol in pairs]


def equivalence(function,module,index):
    original,env,inputs=initial_state(function)
    source_result,source_memory=Source(function,original.fork(),env).execute()
    machine=Machine(module,index,original.fork(),list(env.values()))
    if machine.returns != ([] if source_result is None else [0x7c]):
        raise Unsupported('Source/WASM return ABI mismatch')
    states=machine.execute()
    differences=[]
    for state in states:
        unequal=[]
        if source_result is not None:
            if len(state.stack)!=1:raise Unsupported('Missing target return')
            unequal.append(source_result!=state.stack[0])
        # Compare all caller-visible cells, including read-only inputs and the
        # initial output array. Stack scratch storage is unobservable here.
        for key in original.cells:
            if key not in state.memory.cells:raise Unsupported('Missing target memory cell')
            unequal.append(source_memory.cells[key]!=state.memory.cells[key])
        differences.append(z3.And(state.condition,z3.Or(*unequal)))
    coverage=z3.Or(*[state.condition for state in states])
    mismatch=z3.Or(z3.Not(coverage),*differences)
    return mismatch,inputs,{'paths':len(states),'opcodes':sorted(machine.visited),
                            'sourceCells':len(original.cells),'sourceReturn':source_result is not None}


def flatten(ops):
    for op in ops:
        yield op
        if op.op in {'block','if'}:
            yield from flatten(op.args[0]);yield from flatten(op.args[1])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources',type=Path,default=ROOT/'.wasm-engine/sources')
    parser.add_argument('--sdk',type=Path,default=ROOT/'.wasm-toolchain')
    parser.add_argument('--shipped',type=Path,default=ROOT/'dist/fo.wasm')
    parser.add_argument('--output',type=Path,default=HERE/'evidence')
    args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    # A failed rerun must not leave an apparently current successful report.
    (out/'report.json').write_text(json.dumps({'schema':1,'status':'incomplete','reason':'Validation has not completed'})+'\n')
    contract=json.loads((HERE/'source-contract.json').read_text())
    repo=args.sources/contract['repository']
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
    if head!=contract['commit']:raise Unsupported('Unreviewed upstream revision')
    full=(repo/contract['file']).read_text()
    manifest_path=args.shipped.resolve().with_name('manifest.json')
    lock_path=args.shipped.resolve().with_name('source-lock.json')
    manifest_bytes,lock_bytes=manifest_path.read_bytes(),lock_path.read_bytes()
    manifest,source_lock=json.loads(manifest_bytes),json.loads(lock_bytes)
    if (manifest.get('sourceLockSHA256')!=sha(lock_bytes)
        or manifest.get('sources',{}).get(contract['repository'])!=contract['commit']
        or source_lock.get('files',{}).get(contract['repository'],{}).get(contract['file'])!=sha(full.encode())):
        raise Unsupported('Shipped manifest/source lock does not match verified source')
    sources={name:extract(full,name) for name in contract['functions']}
    for name,source in sources.items():
        if sha(source.encode())!=contract['functions'][name]:raise Unsupported('Source changed: '+name)
    source_path=out/'kernels.cpp'
    source_path.write_text('/* Extracted Project Pluto GPL-2.0-or-later source; see root LICENSE. */\n#include <math.h>\n#define DLL_FUNC\nextern "C" {\n'+'\n\n'.join(sources.values())+'\n}\n')
    sdk=args.sdk.resolve();python=sorted((sdk/'python').glob('*/bin/python3'))[-1]
    emcc=[python,sdk/'upstream/emscripten/emcc.py']
    env={**os.environ,'EM_CONFIG':str(sdk/'.emscripten')}
    sdk_version=(sdk/'upstream/emscripten/emscripten-version.txt').read_text().strip().strip('"')
    if sdk_version!=manifest['emscripten']['version']:raise Unsupported('SDK/manifest version mismatch')
    strict=['-std=c++17','-fno-fast-math','-ffp-contract=off','-g2']
    ast_text=run([*emcc,*strict,'-Xclang','-ast-dump=json','-fsyntax-only',source_path],env)
    nodes=function_nodes(json.loads(ast_text),sources);nodes={name:slim(nodes[name]) for name in sources}
    ast_path=out/'source.ast.json';ast_path.write_text(json.dumps(nodes,indent=2)+'\n')
    modules={}
    commands={}
    for optimization in ['O0','O3']:
        path=out/f'kernels-{optimization}.wasm'
        command=[*emcc,*strict,'-'+optimization,source_path,'-sSTANDALONE_WASM=1','-Wl,--no-entry',
                 *['-Wl,--export='+name for name in sources],'-o',path]
        run(command,env);commands[optimization]=[str(x) for x in command];modules[optimization]=path
    if not args.shipped.exists():raise Unsupported('Shipped module missing; no extracted-only success')
    modules['shipped']=args.shipped.resolve()
    obligations=Obligations(out/'obligations')
    x=z3.FP('sqrt_input',F64)
    obligations.check('lemma-sqrt-zero',z3.fpEQ(z3.fpSqrt(z3.RNE(),x),ZERO)!=z3.fpEQ(x,ZERO))
    module_records={}
    for label,path in modules.items():
        data=path.read_bytes()
        if label=='shipped' and sha(data)!=manifest.get('binarySHA256'):
            raise Unsupported('Shipped binary checksum does not match manifest')
        run(['node','-e','const fs=require("fs");if(!WebAssembly.validate(fs.readFileSync(process.argv[1])))process.exit(1)',path],env)
        module=Module(data)
        module_records[label]={'path':str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
                               'sha256':sha(data),'bytes':len(data),'functions':{}}
        for name,function in nodes.items():
            if label=='shipped' and not module.candidates(name):
                module_records[label]['functions'][name]={'status':'unavailable',
                    'reason':'No retained name/body; possibly inlined or eliminated. Extracted proofs do not validate these inlined production call sites.'}
                continue
            index=module.locate(name);formula,inputs,details=equivalence(function,module,index)
            rewritten=sqrt_zero_rewrite(formula)
            abstract,mapping=congruence_abstraction(rewritten)
            raw=z3.Solver();raw.add(formula)
            (out/'obligations'/(label+'-'+name+'.concrete.smt2')).write_text(raw.to_smt2())
            (out/'obligations'/(label+'-'+name+'.abstraction.json')).write_text(json.dumps(mapping,indent=2)+'\n')
            record=obligations.check(label+'-'+name,abstract,metadata={'dependsOn':['lemma-sqrt-zero'],
                'method':'UNSAT sound congruence overapproximation of concrete IEEE formula; exact substitution round-trip checked',
                'arithmeticTerms':len(mapping),**details})
            _,_,_,ops=module.function(index)
            body=module.bodies[index-len(module.imports)][0]
            (out/(label+'-'+name+'.body.bin')).write_bytes(body)
            module_records[label]['functions'][name]={'status':'verified','index':index,'debugName':module.names.get(index),
                'bodySHA256':sha(module.bodies[index-len(module.imports)][0]),'obligation':record['name']}
        if label=='shipped' and not any(item['status']=='verified' for item in module_records[label]['functions'].values()):
            raise Unsupported('No production function body verified; extracted-only success forbidden')
    from mutations import negative_controls
    negative=negative_controls(nodes,modules['O3'],out,obligations,env)
    if (sha(args.shipped.read_bytes())!=module_records['shipped']['sha256']
        or manifest_path.read_bytes()!=manifest_bytes or lock_path.read_bytes()!=lock_bytes):
        raise Unsupported('Distribution changed during validation; rerun against stable artifacts')
    report={'schema':1,'status':'verified','sourceContract':contract,'sourceSHA256':sha(source_path.read_bytes()),
            'astSHA256':sha(ast_path.read_bytes()),'modules':module_records,'commands':commands,
            'distributionProvenance':{'manifestSHA256':sha(manifest_bytes),'sourceLockSHA256':sha(lock_bytes),
                'upstreamFileSHA256':sha(full.encode()),'emscriptenVersion':sdk_version},
            'checkerSHA256':{name:sha((HERE/name).read_bytes()) for name in ['model.py','wasm.py','verify.py','mutations.py','replay-witness.mjs']},
            'solvers':{'z3':z3.get_version_string(),'cvc5':cvc5.__version__},'obligations':obligations.records,
            'negativeControls':negative,
            'guarantee':'For every modeled binary64 input, return values and caller-visible memory agree between the restricted Clang AST semantics and each actual WASM function body. NaN payload/sign are quotiented out; signed zero, infinities, and subnormals are distinguished.',
            'preconditions':['Arguments are distinct aligned 24-byte double objects, non-overlapping each other and stack; valid wasm32 addresses without wrapping. Disjointness is a verification restriction, not a claim that all C++ aliases are undefined; callers have not been proved to satisfy it.','512 bytes of valid stack scratch; no concurrency, volatile, floating-environment, errno, NaN-payload/sign observation, or caller observation of scratch stack bytes.','IEEE binary64 round-to-nearest ties-to-even operations; sqrt has IEEE sqrt semantics; no fast math or contraction.'],
            'trustedBase':['Source extraction and Clang parser/AST','Custom source interpreter, WASM binary decoder, affine-object memory abstraction, and WASM interpreter','Z3 and independently replaying cvc5; no proof-kernel-checked certificates','Host binary validation; wasm engines implementing the WebAssembly specification'],
            'limits':'Four functions and supported opcodes only; no loops, calls, SIMD, overlapping-object aliases, arbitrary pointer bit operations, or whole-solver/compiler guarantee.'}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Translation evidence: '+str(out/'report.json'))

if __name__=='__main__':main()
