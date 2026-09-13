#!/usr/bin/env python3
"""GPL-2.0-or-later. Validate the actual shipped JPL interpolation CFG slice."""
from __future__ import annotations
import argparse
import copy
import hashlib
import itertools
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path
import cvc5
import z3
from decoder import Module, Reader, function, flatten, locate_slice, decode, Unsupported
from machine import Machine, Ptr, FP, Affine
from source_model import checked, initial, execute, compare
from proofs import establish
import witness

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(data):return hashlib.sha256(data).hexdigest()
def dump(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def command(args,env=None):
    result=subprocess.run([str(a) for a in args],cwd=ROOT,env=env,text=True,capture_output=True,timeout=180)
    if result.returncode:raise RuntimeError(result.stdout+result.stderr)
    return result.stdout

def sdk_python(sdk):
    candidates=sorted((sdk/'python').glob('*/bin/python3'))
    return candidates[-1] if candidates else Path(sys.executable)

def layout(out,sdk):
    source=out/'layout.cpp'
    source.write_text('''// GPL-2.0-or-later. Actual wasm32 C++ layout contract.
#include <cstdio>
#include <cstdint>
#include <cstddef>
#include "jpl_int.h"
static_assert(sizeof(void*)==4 && sizeof(unsigned)==4 && sizeof(double)==8);
static_assert(offsetof(jpl_eph_data,ipt)==48);
static_assert(offsetof(jpl_eph_data,pvsun)==256);
static_assert(offsetof(jpl_eph_data,cache)==336);
static_assert(offsetof(jpl_eph_data,iinfo)==344);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,vel_coeff)==488);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,twot)==632);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,n_posn_avail)==640);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,n_vel_avail)==644);
static_assert(MAX_CHEBY==18);
''')
    python=sdk_python(sdk)
    env={k:v for k,v in os.environ.items() if k not in {'EMCC_CFLAGS','CFLAGS','CXXFLAGS','CPPFLAGS','LDFLAGS'}}
    env['EM_CONFIG']=str(sdk/'.emscripten')
    args=[python,sdk/'upstream/emscripten/em++.py','-std=c++17','-fno-fast-math','-ffp-contract=off','-fsyntax-only',source,'-I',ROOT/'.wasm-engine/sources/jpl_eph']
    command(args,env);return [str(a) for a in args]

def bridge(certificate,expressions,span,guard):
    results=[]
    for profile in certificate['data']['profiles']:
        ncf,ncm,na=profile['ncf'],profile['ncm'],profile['na'];config=(ncf,ncm,na,0,3,2,2,True)
        g,memory,entry,x,dest=initial(config,expressions);actual=memory.clone();machine=Machine(g,actual,entry,x,True)
        machine.sequence(guard)
        if machine.stack.pop()!=1:raise AssertionError('Profile guard rejected')
        machine.execute(span)
        for component in range(ncm):
            cache={}
            def visit(index):
                if index in cache:return cache[index]
                node=certificate['nodes'][index];op=node['op']
                if op=='literal':value=g.literal(node['value'])
                elif op=='input-x':value=x
                elif op=='coefficient':
                    if node['profile']!=profile['name']:raise Unsupported('Cross-profile certificate dependency')
                    value=g.symbol('coefficient_'+str(component*ncf+node['degree']))
                elif op=='exact-scale':
                    if node['step']!=32 or node['na']!=na:raise Unsupported('Certificate scale mismatch')
                    value=g.literal(na/16)
                elif op in ('add','sub','mul'):value=g.operation(op,*[visit(a) for a in node['args']])
                else:raise Unsupported('Unsupported certificate operation')
                cache[index]=value;return value
            for order,kind in enumerate(('position','velocity','acceleration')):
                target=visit(profile['outputs'][kind]);actual_value=actual.get(dest.add(8*(order*ncm+component)),'f64')
                if target!=actual_value:raise AssertionError('Actual production differs from rounded DAG '+profile['name']+'/'+kind)
                results.append({'profile':profile['name'],'component':component,'quantity':kind,'certificateNode':profile['outputs'][kind],
                                'normalizedExpressionSHA256':g.fingerprint(target)})
    return results

def mutations(data,params,locals,span,guard,out,expressions):
    config=(7,3,1,0,3,2,2,True);g,memory,entry,x,dest=initial(config,expressions)
    begin,end=span[0].start,span[-1].end;raw=data[begin:end];raw_guard=data[guard[0].start:guard[-1].end]
    original=witness.wrapper(params,locals,entry,g,raw,raw_guard)
    candidates=[('position-multiply-to-add',next(o for o in flatten(span) if o.name=='f64.mul'),0xa0),
                ('position-subtract-to-add',next(o for o in flatten(span) if o.name=='f64.sub'),0xa0),
                ('velocity-branch-inverted',next(o for o in flatten(span) if o.name=='i32.lt_s'),0x4a)]
    records=[]
    for name,op,replacement in candidates:
        changed=bytearray(raw);changed[op.start-begin]=replacement
        reader=Reader(bytes(changed)+b'\x0b',begin);bad,endcode=decode(reader);reader.end()
        model=memory.clone();execute(model,config,expressions,x,dest)
        try:
            machine=Machine(g,memory.clone(),entry,x,True);machine.execute(bad);compare(model,machine.memory)
        except (AssertionError,Unsupported) as exc:reason=str(exc)
        else:raise AssertionError('Bad production mutation accepted '+name)
        mutant=witness.wrapper(params,locals,entry,g,bytes(changed),raw_guard)
        actual=witness.execute(out,name,original,mutant,memory)
        records.append({'name':name,'productionByteOffset':op.start,'fromOpcode':op.name,'rejected':True,'reason':reason,'actualWasmWitness':actual})
    # Memory and unsupported-op gates are independently exercised on real ops.
    for name,op,change in [('out-of-domain-twot-load',next(o for o in flatten(span) if o.name=='f64.load' and o.args[1]==632),'memory'),
                           ('unsupported-opcode',next(o for o in flatten(span) if o.name=='f64.mul'),'unsupported')]:
        bad=copy.deepcopy(span)
        target=next(o for o in flatten(bad) if o.start==op.start)
        if change=='memory':target.args=(target.args[0],4096)
        else:target.name='f64.min'
        try:Machine(g,memory.clone(),entry,x,True).execute(bad)
        except Unsupported as exc:reason=str(exc)
        else:raise AssertionError('Unsupported/memory mutation accepted')
        records.append({'name':name,'productionByteOffset':op.start,'rejected':True,'reason':reason})
    return records

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shipped',type=Path,default=ROOT/'dist/fo.wasm');parser.add_argument('--sdk',type=Path,default=ROOT/'.wasm-toolchain')
    parser.add_argument('--output',type=Path,default=HERE/'evidence');args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    dump(out/'report.json',{'status':'incomplete','passed':False})
    if sys.flags.optimize:raise RuntimeError('Optimized Python forbidden')
    source_dir=ROOT/'.wasm-engine/sources/jpl_eph';manifest_path=args.shipped.parent/'manifest.json';lock_path=args.shipped.parent/'source-lock.json'
    certificate_path=ROOT/'verification/ephemeris/evidence/certificate.json'
    sdk=args.sdk.resolve()
    node=shutil.which('node')
    if node is None:raise RuntimeError('Node.js is required for bytecode validation and mutation witnesses')
    inputs=[args.shipped,manifest_path,lock_path,source_dir/'jpleph.cpp',source_dir/'jpl_int.h',certificate_path,
            ROOT/'verification/ephemeris/source-contract.json',ROOT/'verification/ephemeris/source.py',
            *[ROOT/'verification/translation'/name for name in ('wasm.py','model.py','verify.py')],
            *HERE.glob('*.py'),HERE/'witness.mjs',sdk/'upstream/bin/clang',sdk/'upstream/emscripten/em++.py',
            sdk/'upstream/emscripten/emcc.py',sdk/'.emscripten',sdk_python(sdk),Path(sys.executable),Path(node)]
    hashes={str(p.resolve().relative_to(ROOT)) if p.resolve().is_relative_to(ROOT) else str(p.resolve()):sha(p.read_bytes()) for p in inputs}
    data=args.shipped.read_bytes();manifest=json.loads(manifest_path.read_text());lock=json.loads(lock_path.read_text())
    if sha(data)!=manifest['binarySHA256'] or sha(lock_path.read_bytes())!=manifest['sourceLockSHA256']:raise RuntimeError('Distribution provenance mismatch')
    for name in ('jpleph.cpp','jpl_int.h'):
        if sha((source_dir/name).read_bytes())!=lock['files']['jpl_eph'][name]:raise RuntimeError('Source differs from shipping lock')
    expressions,contract=checked(source_dir)
    if manifest['sources']['jpl_eph']!=contract['commit']:raise RuntimeError('Upstream revision mismatch')
    command(['node','-e','const b=require("fs").readFileSync(process.argv[1]);if(!WebAssembly.validate(b))process.exit(1)',args.shipped])
    regressions=json.loads(command([sys.executable,HERE/'test_checker.py',args.shipped]))
    if not regressions.get('passed'):raise AssertionError('Checker regressions did not pass')
    layout_command=layout(out,sdk);proofs=establish(out/'obligations')
    module=Module(data);index=module.locate('jpl_state');params,returns,locals,ops=function(module,index)
    branch,span,guard,path=locate_slice(ops)
    expected_guard=[('local.get',(6,)),('i32.load',(2,8)),('local.get',(12,)),('i32.eq',()),('i32.const',(0,)),('local.get',(19,)),('select',())]
    if [(o.name,o.args) for o in guard]!=expected_guard:raise Unsupported('Selection predicate does not match its proved instruction model')
    raw_body,body_offset=module.bodies[index-len(module.imports)]
    (out/'jpl_state.body.bin').write_bytes(raw_body);(out/'interp-slice.bin').write_bytes(data[span[0].start:span[-1].end])
    if params!=[0x7f,0x7c,0x7f,0x7f,0x7f,0x7f] or returns!=[0x7f]:raise Unsupported('Unexpected production ABI')
    prefix_end=next(i for i,op in enumerate(span) if op.name=='block')
    prefix,core=span[:prefix_end],span[prefix_end:]
    visited=set();edges=set();live=set();case_records=[];max_steps=0;start=time.monotonic()
    for ncf in range(6,15):
        for (ncm,body),flag in itertools.product(((1,13),(2,10),(3,0),(3,14)),range(1,4)):
            cache_cases=[(2,2,True)]+[(np,nv,False) for np in range(2,18) for nv in range(2,np+1)]
            for np,nv,cold in cache_cases:
                config=(ncf,ncm,8,0,flag,np,nv,cold);g,memory,entry,x,dest=initial(config,expressions,True,body)
                actual=memory.clone();machine=Machine(g,actual,entry,x,cold);machine.sequence(guard)
                if machine.stack.pop()!=1:raise AssertionError('Actual selection guard failed')
                machine.execute(prefix)
                if machine.memory.writes:raise Unsupported('Setup prefix must not mutate memory before compositional comparison')
                machine.written_locals=set();machine.entry_reads=set()
                machine.execute(core);execute(memory,config,expressions,x,dest,True);compare(memory,actual)
                if machine.cache_tests!=1:raise Unsupported('Missing/extra cache comparison')
                visited|=machine.visited;edges|=machine.edges;max_steps=max(max_steps,machine.steps)
                live|=machine.entry_reads
                digest=sha(repr((g.nodes,sorted((str(k),str(v)) for k,v in actual.cells.items() if k[0]!='stack'))).encode())
                case_records.append({'ncf':ncf,'ncm':ncm,'representativeBody':body,'quantities':flag,'positionPrefix':np if not cold else 'arbitrary-i32',
                                     'velocityPrefix':nv if not cold else 'arbitrary-i32','cold':cold,'semanticStateSHA256':digest,'executedInstructions':machine.steps})
        print(f'Production interp: ncf={ncf}, {len(case_records)} universal symbolic cases checked',flush=True)
    certificate=json.loads(certificate_path.read_text())
    # Exhaust actual body/destination selection before composing the verified
    # arithmetic core. Compare precisely the locals the core reads before any
    # assignment, over every enumerated control path; unused locals may differ.
    setups=0
    for ncf,body,flag in itertools.product(range(6,15),range(15),range(1,4)):
        ncm=2 if body==10 else 1 if body==13 else 3
        representative=body if ncm!=3 else 14 if body==14 else 0
        config=(ncf,ncm,8,0,flag,2,2,True)
        g,mem,entry,x,_=initial(config,expressions,True,representative)
        baseline=Machine(g,mem,entry,x,True);baseline.execute(prefix)
        for pointer in sorted({p['pointer'] for p in certificate['data']['profiles']}):
            g,memory,entry,x,_=initial(config,expressions,True,body,pointer)
            setup=Machine(g,memory,entry,x,True);setup.sequence(guard)
            if setup.stack.pop()!=1:raise AssertionError('Alternate actual body guard failed')
            setup.execute(prefix)
            if setup.memory.writes:raise Unsupported('Alternate setup prefix mutates memory')
            if any(setup.locals.get(k)!=baseline.locals.get(k) for k in live):
                raise AssertionError('Body/record setup changes a live arithmetic-core input')
            setups+=1
    bridges=bridge(certificate,expressions,span,guard)
    negative=mutations(data,params,locals,span,guard,out,expressions)
    dump(out/'cases.json',case_records);dump(out/'dag-bridge.json',bridges)
    all_ops=list(flatten(span));coverage={'decodedInstructions':len(all_ops),'executedInstructionOffsets':sorted(visited),
        'unreachedInstructionOffsets':sorted(o.start for o in all_ops if o.start not in visited),'branchEdges':[list(x) for x in sorted(edges)],'maxInstructionsPerCase':max_steps}
    coverage['coreEntryLocalsReadBeforeAssignment']=sorted(live);coverage['setupCorrespondences']=setups
    dump(out/'coverage.json',coverage)
    for p in inputs:
        key=str(p.resolve().relative_to(ROOT)) if p.resolve().is_relative_to(ROOT) else str(p.resolve())
        if sha(p.read_bytes())!=hashes[key]:raise RuntimeError('Input changed during production validation: '+key)
    report={'schema':1,'status':'verified','passed':True,'inputsSHA256':hashes,'layoutCompilerCommand':layout_command,
      'software':{'python':sys.version,'z3':z3.get_version_string(),'cvc5':cvc5.__version__,'node':command([node,'--version']).strip()},
      'production':{'function':'jpl_state','index':index,'bodyOffset':body_offset,'bodyBytes':len(raw_body),'bodySHA256':sha(raw_body),
        'sliceStart':span[0].start,'sliceEndExclusive':span[-1].end,'sliceBytes':span[-1].end-span[0].start,
        'sliceSHA256':sha(data[span[0].start:span[-1].end]),'cfgPath':path,'guardStart':guard[0].start,'guardEndExclusive':guard[-1].end},
      'symbolicCases':len(case_records),'setupCorrespondences':setups,'elapsedSeconds':time.monotonic()-start,'dagBridgeComponentBounds':len(bridges),
      'solverObligations':proofs,'negativeControls':negative,'checkerRegressions':regressions,'caseEvidenceSHA256':sha((out/'cases.json').read_bytes()),
      'coverageSHA256':sha((out/'coverage.json').read_bytes()),'dagBridgeSHA256':sha((out/'dag-bridge.json').read_bytes()),
      'domain':{'ncf':'6..14','ncm':'1..3','quantities':'1..3','na':[1,2,4,8],'subinterval':'symbolic L, 0<=L<na',
        'warmCacheCounters':'2<=n_vel_avail<=n_posn_avail<=17','coldCacheCounters':'arbitrary i32 values; overwritten before read',
        'floatingInputs':'all binary64 coefficient/cache encodings modulo NaN payload/sign; tc finite in [-1,1]; warm fp.eq(cached_tc,tc), cold not fp.eq(cached_tc,tc)',
        'scale':'symbolic binary64 vfac; numeric-bound application requires exact vfac=(2*na)/32',
        'buffers':'valid aligned disjoint coefficient/output/stack storage; output has ncm*quantities doubles; ephemeris fields use checked wasm32 layout; no address wrap'},
      'guarantee':'The selected actual production CFG slice preserves pinned source interp cache updates and all caller-visible floating outputs, under its entry-state/domain assumptions; arithmetic proof is symbolic, integer control exhaustive.',
      'entryBoundary':'At the unique selected interpolation branch, after outer jpl_state date/modf/subinterval setup. Caller local-to-source mappings, successful I/O/cache record selection, and entry tc/vfac correctness are preconditions. The actual branch guard and all selected slice control are executed/validated.',
      'numericBridge':'All 114 profile/component/quantity DAG expressions equal actual production output expressions for cold/recomputed interpolation. Applying existing forward bounds also requires coefficient envelopes, correct input tc, the rounding premise, and valid warm numerical cache prefixes. The comparison quotients NaN payload/sign and assumes they are not observed.',
      'trustedBase':['Pinned-source narrow parser and reviewed source loop model','Binary decoder, bounded interpreter, affine-object memory model, exhaustive enumerator and congruence normalizer',
        'Z3 and cvc5 for retained SMT lemmas','Reviewed correspondence of explicit classified add/mul numeric rules to WebAssembly/IEEE64 semantics; the direct native-FP commutativity queries timed out and are NOT counted',
        'Host binary validator and WebAssembly engine for negative witnesses','C++ frontend for layout assertions'],
      'limits':['Not a proof of whole jpl_state or the complete solver/compiler','No proof of reachability/entry mappings from function start, date/modf selection, I/O, absolute memory allocation or concurrency',
        'No km-to-AU, barycentric subtraction, Earth/Moon combinations or physical ephemeris accuracy bound','Existing DAG kernel proofs and rounding premise have separate reports; this checker does not kernel-check its own interpreters',
        'Warm arithmetic cache prefix correctness is external to numerical-bound application; translation equivalence itself permits arbitrary cached floating values']}
    dump(out/'report.json',report);print(f'PASS: {len(case_records)} symbolic production cases; {len(bridges)} exact DAG correspondences; {len(negative)} negative controls',flush=True)

if __name__=='__main__':main()
