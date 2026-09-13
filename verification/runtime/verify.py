#!/usr/bin/env python3
"""GPL-2.0-or-later. Validate production quad conversion/shift instructions."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import z3

from machine import Module, Machine, Value, integer, Unsupported, clz
import cvc5

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
NAMES = ['__ashlti3','__lshrti3','__extenddftf2','__trunctfdf2']


def sha(data): return hashlib.sha256(data).hexdigest()


def cvc(smt, extended_fp=False):
    solver=cvc5.Solver(); solver.setOption('tlimit-per','60000')
    if extended_fp: solver.setOption('fp-exp','true')
    parser=cvc5.InputParser(solver)
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6,'(set-logic ALL)\n'+smt,'runtime')
    answers=[]
    while True:
        command=parser.nextCommand()
        if command.isNull(): break
        answer=command.invoke(solver,parser.getSymbolManager()).strip()
        if answer: answers.append(answer)
    if len(answers)!=1 or answers[0] not in {'sat','unsat','unknown'}:
        raise RuntimeError('Unexpected cvc5 response: '+repr(answers))
    return answers[0]


class Checks:
    def __init__(self, out):
        self.out=out; self.records=[]; out.mkdir(parents=True,exist_ok=True)

    def check(self, name, formula, expected='unsat', extended_fp=False):
        solver=z3.Solver(); solver.set(timeout=60000); solver.add(formula)
        smt=solver.to_smt2(); (self.out/(name+'.smt2')).write_text(smt)
        start=time.monotonic(); answer=str(solver.check()); elapsed=time.monotonic()-start
        if answer!=expected:
            raise RuntimeError(f'{name}: Z3 {answer}, expected {expected}; '+solver.reason_unknown())
        start=time.monotonic(); other=cvc(smt,extended_fp); other_elapsed=time.monotonic()-start
        if other!=expected: raise RuntimeError(f'{name}: cvc5 {other}, expected {expected}')
        item={'name':name,'z3':answer,'cvc5':other,'smt2SHA256':sha(smt.encode()),
              'z3Seconds':elapsed,'cvc5Seconds':other_elapsed,'cvc5ExtendedFP':extended_fp}
        self.records.append(item); print(name+': '+answer+'/'+other,flush=True)
        return solver.model() if expected=='sat' else None


def u64(value): return z3.ZeroExt(32,value)


def context(module, extra=z3.BoolVal(True)):
    stack,lower,upper,out=z3.BitVecs('stack lower upper out',32)
    memory=z3.Array('initial_memory',z3.BitVecSort(32),z3.BitVecSort(8))
    size=module.memories[0][0]*65536
    pre=z3.And(z3.UGE(stack,32),z3.ULE(lower,stack-32),z3.ULE(stack,upper),
               z3.ULE(u64(upper),size),z3.ULE(u64(out)+16,size),
               z3.Or(z3.ULE(u64(out)+16,u64(stack)-32),z3.UGE(out,stack)),extra)
    globals_=[Value('i32',z3.BitVec('global_'+str(i),32)) for i in range(len(module.globals))]
    if len(globals_)!=5 or module.global_names.get(0)!='__stack_pointer':
        raise Unsupported('Unreviewed stack instrumentation globals')
    globals_[0]=Value('i32',stack);globals_[3]=Value('i32',upper);globals_[4]=Value('i32',lower)
    return pre,memory,globals_,out,stack,size


def load128(memory,pointer):
    return z3.Concat(*[z3.Select(memory,pointer+i) for i in reversed(range(16))])


def widened_bits(bits):
    """Source-level interchange-field specification, independently IEEE-checked."""
    sign=z3.ZeroExt(64,bits & (1<<63))<<64
    exponent=z3.LShR(bits,52)&2047
    fraction=bits&((1<<52)-1)
    wide=z3.ZeroExt(64,fraction)
    normal=(z3.ZeroExt(64,exponent)+15360)<<112 | wide<<60
    special=z3.BitVecVal(32767<<112,128) | wide<<60
    scale=clz(fraction)-11
    sub=(z3.ZeroExt(64,15361-scale)<<112) | ((wide << (z3.ZeroExt(64,scale)+60)) ^ (1<<112))
    return sign | z3.If(exponent==2047,special,z3.If(exponent!=0,normal,z3.If(fraction==0,z3.BitVecVal(0,128),sub)))


def numeric_conversion(bits, target, output):
    source=z3.fpBVToFP(bits,z3.FPSort(15,113) if bits.size()==128 else z3.Float64())
    converted=z3.fpToFP(z3.RNE(),source,target)
    # SMT floating equality distinguishes signed zeros; non-NaN encodings are
    # unique. Avoid Z3's nonstandard fp.to_ieee_bv extension so cvc5 replays it.
    return z3.Implies(z3.Not(z3.fpIsNaN(source)),z3.fpBVToFP(output,target)==converted)


def narrowed_bits(bits):
    """Direct interchange-format rounding, not the compiler's sticky-shift code.

    Decode a positive significand and round once to the target quantum. In the
    subnormal case the quantum is fixed at 2^-1074. The normal target discards
    sixty significand bits. Integer increment naturally carries into exponent.
    """
    sign=z3.ZeroExt(63,z3.Extract(127,127,bits))<<63
    exponent=z3.ZeroExt(17,z3.Extract(126,112,bits))
    fraction=bits & ((1<<112)-1)
    def nearest_shift(value, amount):
        wide_amount=z3.ZeroExt(96,amount)
        whole=z3.LShR(value,wide_amount)
        remainder=value & ((z3.BitVecVal(1,128)<<wide_amount)-1)
        half=z3.BitVecVal(1,128)<<(wide_amount-1)
        increment=z3.If(z3.Or(z3.UGT(remainder,half),z3.And(remainder==half,whole&1==1)),z3.BitVecVal(1,128),z3.BitVecVal(0,128))
        return whole+increment
    normal=(z3.ZeroExt(32,exponent-15360)<<52)+z3.Extract(63,0,nearest_shift(fraction,z3.BitVecVal(60,32)))
    significand=fraction | z3.If(exponent==0,z3.BitVecVal(0,128),z3.BitVecVal(1<<112,128))
    distance=15421-z3.If(exponent==0,z3.BitVecVal(1,32),exponent)
    subnormal=z3.If(z3.UGT(distance,113),z3.BitVecVal(0,64),z3.Extract(63,0,nearest_shift(significand,distance)))
    nan=z3.BitVecVal((2047<<52)|(1<<51),64) | z3.ZeroExt(13,z3.Extract(110,60,bits))
    magnitude=z3.If(z3.And(exponent==32767,fraction!=0),nan,
                   z3.If(z3.UGE(exponent,17407),z3.BitVecVal(2047<<52,64),
                         z3.If(z3.UGE(exponent,15361),normal,subnormal)))
    return sign|magnitude


def output_refinement(name,bits,result):
    if name=='__extenddftf2':
        return result==widened_bits(bits)
    return result==narrowed_bits(bits)


def verify_one(name,module,checks,indices):
    lo,hi=z3.BitVecs('lo hi',64); shift=z3.BitVec('shift',32)
    extra=z3.ULT(shift,128) if name in NAMES[:2] else z3.BoolVal(True)
    pre,memory,globals_,out,stack,size=context(module,extra)
    machine=Machine(module,pre,size,set(indices.values()))
    bits=z3.Concat(hi,lo)
    if name in NAMES[:2]: arguments=[Value('i32',out),Value('i64',lo),Value('i64',hi),Value('i32',shift)]
    elif name=='__extenddftf2': arguments=[Value('i32',out),Value('f64',lo)];bits=lo
    else: arguments=[Value('i64',lo),Value('i64',hi)]
    print('Symbolic production execution: '+name,flush=True)
    states=machine.invoke(indices[name],arguments,memory,globals_)
    checks.check(name+'-path-coverage',z3.And(pre,z3.Not(z3.Or(*[s.condition for s in states]))))
    checks.check(name+'-memory-bounds',z3.Or(*[z3.And(pre,path,z3.Not(valid)) for path,valid,*_ in machine.accesses]))
    differences=[]
    point=z3.BitVec('observed_address',32)
    outside=z3.And(z3.Or(z3.ULT(point,out),z3.UGE(u64(point),u64(out)+16)),
                   z3.Or(z3.ULT(u64(point),u64(stack)-32),z3.UGE(point,stack)))
    if name=='__trunctfdf2':
        outside=z3.Or(z3.ULT(u64(point),u64(stack)-32),z3.UGE(point,stack))
    for state in states:
        result=state.stack[0].bits if name=='__trunctfdf2' else load128(state.memory,out)
        if name=='__ashlti3': specification=result==bits<<z3.ZeroExt(96,shift)
        elif name=='__lshrti3': specification=result==z3.LShR(bits,z3.ZeroExt(96,shift))
        else: specification=output_refinement(name,bits,result)
        differences.append(z3.And(state.condition,z3.Not(specification)))
    checks.check(name+'-result',z3.And(pre,z3.Or(*differences)))
    checks.check(name+'-frame-and-globals',z3.And(pre,z3.Or(*[
        z3.And(state.condition,z3.Or(z3.And(outside,z3.Select(state.memory,point)!=z3.Select(memory,point)),
                                   *[a.bits!=b.bits for a,b in zip(state.globals,globals_)])) for state in states])))
    index=indices[name];body=module.bodies[index-len(module.imports)][0]
    (checks.out.parent/(name+'.body.bin')).write_bytes(body)
    return {'name':name,'index':index,'bodySHA256':sha(body),'bodyBytes':len(body),'paths':len(states),
            'memoryAccesses':len(machine.accesses),'calledIndices':sorted({b for _,b in machine.calls}),
            'visitedInstructions':[{'function':i,'byteOffset':o,'opcode':n} for i,o,n in sorted(machine.visited)]}


def main():
    out=HERE/'evidence';out.mkdir(parents=True,exist_ok=True)
    report_path=out/'report.json';report_path.write_text('{"passed":false,"status":"incomplete"}\n')
    if sys.flags.optimize: raise RuntimeError('Optimized Python is forbidden')
    paths=[HERE/'machine.py',HERE/'verify.py',ROOT/'verification/translation/wasm.py',
           ROOT/'verification/translation/model.py',ROOT/'dist/manifest.json']
    source_root=ROOT/'.wasm-toolchain/upstream/emscripten/system/lib/compiler-rt/lib/builtins'
    runtime_sources=['extenddftf2.c','trunctfdf2.c','fp_extend_impl.inc','fp_trunc_impl.inc',
                     'ashlti3.c','lshrti3.c','int_lib.h','int_types.h']
    paths += [source_root/name for name in runtime_sources]
    before={p:p.read_bytes() for p in paths}
    data=(ROOT/'dist/fo.wasm').read_bytes()
    manifest=json.loads((ROOT/'dist/manifest.json').read_text())
    if sha(data)!=manifest['binarySHA256']: raise RuntimeError('Production manifest mismatch')
    subprocess.run(['node','-e','if(!WebAssembly.validate(require("fs").readFileSync(process.argv[1])))process.exit(1)',str(ROOT/'dist/fo.wasm')],check=True)
    module=Module(data);indices={name:module.locate(name) for name in NAMES}
    checks=Checks(out/'obligations')
    records=[verify_one(name,module,checks,indices) for name in NAMES]
    bits=z3.BitVec('binary64_input',64)
    checks.check('widening-field-spec-is-IEEE',z3.Not(numeric_conversion(bits,z3.FPSort(15,113),widened_bits(bits))),extended_fp=True)
    quad=z3.BitVec('binary128_input',128)
    checks.check('narrowing-field-spec-is-IEEE',z3.Not(numeric_conversion(quad,z3.Float64(),narrowed_bits(quad))),extended_fp=True)
    exponent=z3.Extract(62,52,bits);fraction=z3.Extract(51,0,bits)
    roundtrip=z3.If(z3.And(exponent==2047,fraction!=0),bits|(1<<51),bits)
    checks.check('binary64-roundtrip-and-NaN-policy',narrowed_bits(widened_bits(bits))!=roundtrip)
    if (ROOT/'dist/fo.wasm').read_bytes()!=data: raise RuntimeError('Production module changed')
    if any(p.read_bytes()!=content for p,content in before.items()): raise RuntimeError('Runtime proof inputs changed')
    report={'schema':1,'passed':True,'status':'complete','binarySHA256':sha(data),'functions':records,
            'checks':checks.records,'versions':{'z3':z3.get_version_string(),'cvc5':cvc5.__version__},
            'checkerSHA256':{name:sha((HERE/name).read_bytes()) for name in ['machine.py','verify.py']},
            'inputSHA256':{str(p.relative_to(ROOT)):sha(content) for p,content in before.items()},
            'runtimeSourceCorrespondence':'Source hashes identify the pinned compiler-rt implementation for audit. The theorem validates retained WASM instructions directly against a bit-field specification; no C AST-to-WASM proof is inferred from these hashes.',
            'solverBoundary':'Actual instruction-to-bitvector specification checks use both solvers in their normal modes. The two IEEE-FP128 specification bridges additionally enable cvc5 fp-exp; cvc5 labels this mode experimental with known issues. These corroborate Z3 but are not independently kernel-checked certificates.',
            'scope':'Universal direct production WASM instruction refinement for retained 128-bit shifts and binary64/binary128 conversions. Explicit valid disjoint output/stack regions, 32-byte stack reserve, current minimum memory size, and initialized stack instrumentation bounds. No C AST or whole-runtime/compiler proof.'}
    report_path.write_text(json.dumps(report,indent=2)+'\n')
    print('Production runtime verification passed',flush=True)


if __name__=='__main__': main()
