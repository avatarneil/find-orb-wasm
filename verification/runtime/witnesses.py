#!/usr/bin/env python3
"""GPL-2.0-or-later. Execute unchanged production bodies and SAT mutants."""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
import z3

from machine import Module, Reader, Machine, Value, integer
from verify import ROOT, HERE, NAMES, Checks, context, load128, widened_bits, narrowed_bits, sha


def leb(number):
    result = bytearray()
    while number >= 128:
        result.append((number & 127) | 128); number >>= 7
    return bytes(result + bytes([number]))


def vector(items):
    return leb(len(items)) + b''.join(items)


def string(value):
    data = value.encode(); return leb(len(data)) + data


def adapter(data):
    """Append raw-bit test wrappers; preserve every existing function body."""
    module = Module(data)
    indices = {name: module.locate(name) for name in NAMES}
    reader = Reader(data); reader.take(8); sections = []
    while reader.remaining():
        kind = reader.byte(); payload = reader.take(reader.leb()); sections.append((kind, payload))
    new_types = [b'\x60\x02\x7f\x7e\x00', b'\x60\x02\x7e\x7e\x01\x7e']
    first_type = len(module.types); first_function = len(module.imports) + len(module.bodies)
    bodies = [b'\x00\x20\x00\x20\x01\xbf\x10' + leb(indices['__extenddftf2']) + b'\x0b',
              b'\x00\x20\x00\x20\x01\x10' + leb(indices['__trunctfdf2']) + b'\xbd\x0b']
    exports = [string(name) + b'\x00' + leb(indices[name]) for name in NAMES[:2]]
    exports += [string(name) + b'\x00' + leb(first_function+i) for i, name in enumerate(NAMES[2:])]
    additions = {1: new_types, 3: [leb(first_type), leb(first_type+1)], 7: exports,
                 10: [leb(len(body))+body for body in bodies]}
    output = bytearray(data[:8])
    for kind, payload in sections:
        if kind in additions:
            reader = Reader(payload); count = reader.leb()
            payload = leb(count+len(additions[kind])) + payload[reader.pos:] + b''.join(additions[kind])
        output += bytes([kind]) + leb(len(payload)) + payload
    adapted = Module(bytes(output))
    if [b for b, _ in adapted.bodies[:-2]] != [b for b, _ in module.bodies]:
        raise RuntimeError('Adapter changed production instructions')
    return bytes(output)


def expected(name, lo, hi=0, shift=0):
    bits = (hi << 64) | lo
    if name == '__ashlti3': return (bits << shift) & ((1 << 128)-1)
    if name == '__lshrti3': return bits >> shift
    value = widened_bits(z3.BitVecVal(lo, 64)) if name == '__extenddftf2' else narrowed_bits(z3.BitVecVal(bits, 128))
    return z3.simplify(value).as_long()


def case(name, lo, hi=0, shift=0):
    return {'name': name, 'lo': str(lo), 'hi': str(hi), 'shift': shift,
            'expected': str(expected(name, lo, hi, shift))}


def main():
    out = HERE/'evidence'; report_path = out/'witnesses.json'
    report_path.write_text('{"passed":false,"status":"incomplete"}\n')
    before = {p: p.read_bytes() for p in [ROOT/'dist/fo.wasm', HERE/'machine.py', HERE/'verify.py',
                                        HERE/'witnesses.py', HERE/'replay.mjs']}
    data = before[ROOT/'dist/fo.wasm']; module = Module(data)
    original = json.loads((out/'report.json').read_text())
    if not original.get('passed') or original['binarySHA256'] != sha(data):
        raise RuntimeError('Fresh production proof required')
    if any(sha((HERE/name).read_bytes()) != value for name,value in original['checkerSHA256'].items()):
        raise RuntimeError('Production checker changed since proof; rerun verify.py')
    work = ROOT/'.cache/runtime-witnesses'; work.mkdir(exist_ok=True)
    checks = Checks(out/'negative-obligations')
    indices = {name: module.locate(name) for name in NAMES}
    original_path = work/'original.wasm'; original_path.write_bytes(adapter(data))
    vectors = []
    for sign in [0, 1]:
        for exponent in [0, 1, 2, 1022, 1023, 2046, 2047]:
            for fraction in [0, 1, 1 << 51, (1 << 52)-1]:
                vectors.append(case('__extenddftf2', sign << 63 | exponent << 52 | fraction))
        for exponent in [0, 1, 15359, 15360, 15361, 15362, 16383, 17406, 17407, 32766, 32767]:
            for fraction in [0, 1, (1 << 59)-1, 1 << 59, (1 << 59)+1,
                             (1 << 60)+(1 << 59), (1 << 112)-1]:
                bits = sign << 127 | exponent << 112 | fraction
                vectors.append(case('__trunctfdf2', bits & ((1 << 64)-1), bits >> 64))
    for name in NAMES[:2]:
        for shift in [0, 1, 31, 32, 63, 64, 65, 95, 96, 127]:
            for lo, hi in [(0, 0), (1, 0), (0, 1), ((1 << 64)-1, (1 << 64)-1),
                           (0x0123456789abcdef, 0xfedcba9876543210)]:
                vectors.append(case(name, lo, hi, shift))
    jobs = [{'module': str(original_path), 'cases': vectors, 'kind': 'original'}]
    mutations = []
    for name, old_op, new_code in [('__ashlti3', 'i64.shl', 0x88),
                                   ('__lshrti3', 'i64.shr_u', 0x86),
                                   ('__extenddftf2', 'i64.add', 0x7d),
                                   ('__trunctfdf2', 'i64.add', 0x7d)]:
        record = next(item for item in original['functions'] if item['name'] == name)
        instruction = next(item for item in record['visitedInstructions']
                           if item['function'] == indices[name] and item['opcode'] == old_op)
        changed = bytearray(data); changed[instruction['byteOffset']] = new_code
        changed = bytes(changed); mutant = Module(changed)
        lo, hi = z3.BitVecs('lo hi', 64); shift = z3.BitVec('shift', 32)
        pre, memory, globals_, outptr, stack, size = context(mutant,
            z3.ULT(shift, 128) if name in NAMES[:2] else z3.BoolVal(True))
        pre = z3.And(pre, outptr == 4096, stack == module.globals[0],
                     globals_[3].bits == module.globals[0], globals_[4].bits == 1024)
        machine = Machine(mutant, pre, size, set(indices.values()))
        args = ([Value('i32', outptr), Value('i64', lo), Value('i64', hi), Value('i32', shift)]
                if name in NAMES[:2] else [Value('i32', outptr), Value('f64', lo)]
                if name == '__extenddftf2' else [Value('i64', lo), Value('i64', hi)])
        states = machine.invoke(indices[name], args, memory, globals_)
        bits = z3.Concat(hi, lo)
        spec = (bits << z3.ZeroExt(96, shift) if name == '__ashlti3' else
                z3.LShR(bits, z3.ZeroExt(96, shift)) if name == '__lshrti3' else
                widened_bits(lo) if name == '__extenddftf2' else narrowed_bits(bits))
        violation = z3.Or(*[z3.And(s.condition,
            (s.stack[0].bits if name == '__trunctfdf2' else load128(s.memory, outptr)) != spec)
            for s in states])
        model = checks.check(name+'-mutated-result', z3.And(pre, violation), expected='sat')
        value = lambda item: model.eval(item, model_completion=True).as_long()
        witness = case(name, value(lo), value(hi), value(shift) if name in NAMES[:2] else 0)
        path = work/(name+'-mutated.wasm'); path.write_bytes(adapter(changed))
        jobs += [{'module': str(original_path), 'cases': [witness], 'kind': 'original-witness'},
                 {'module': str(path), 'cases': [witness], 'kind': 'mutant'}]
        mutations.append({'name': name, 'byteOffset': instruction['byteOffset'],
                          'originalOpcode': old_op, 'mutantOpcodeByte': new_code,
                          'mutatedBinarySHA256': sha(changed), 'witness': witness})
    input_path = work/'jobs.json'; input_path.write_text(json.dumps(jobs)+'\n')
    result = subprocess.run(['node', str(HERE/'replay.mjs'), str(input_path)],
                            check=True, text=True, capture_output=True, timeout=120)
    replay = json.loads(result.stdout)
    if any(p.read_bytes() != contents for p, contents in before.items()):
        raise RuntimeError('Witness inputs changed during execution')
    report_path.write_text(json.dumps({'passed': True, 'status': 'complete',
        'binarySHA256': sha(data), 'inputSHA256': {str(p.relative_to(ROOT)): sha(b) for p,b in before.items()},
        'finiteCases': len(vectors), 'mutations': mutations, 'checks': checks.records, 'replay': replay,
        'scope': 'Execution corroboration of unchanged production bodies and four actual opcode mutations. Raw-bit WASM wrappers avoid JavaScript NaN payload conversion. Finite cases share the bit-field specification with the universal proof and are not independent proofs.'}, indent=2)+'\n')
    print(f'{len(vectors)} original cases and four dual-SAT mutation witnesses executed in Node')


if __name__ == '__main__': main()
