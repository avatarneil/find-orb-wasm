#!/usr/bin/env python3
"""GPL-2.0-or-later. Regression tests for the additional trusted interpreter."""
import unittest
from unittest.mock import patch
import z3
from machine import Module, Machine, Value, integer, Unsupported, Reader, decode, clz
from witnesses import leb, vector


def module(body, params=b'', returns=b'\x7e'):
    sections = [(1, vector([b'\x60'+leb(len(params))+params+leb(len(returns))+returns])),
                (3, vector([b'\x00'])), (5, b'\x01\x00\x01'),
                (10, vector([leb(len(body)+1)+b'\x00'+body]))]
    return Module(b'\x00asm\x01\x00\x00\x00'+b''.join(bytes([k])+leb(len(v))+v for k,v in sections))


def run(body, args=(), params=b'', returns=b'\x7e'):
    code=module(body,params,returns)
    memory=z3.Array('test_memory',z3.BitVecSort(32),z3.BitVecSort(8))
    machine=Machine(code,z3.BoolVal(True),65536,{0})
    states=machine.invoke(0,list(args),memory,[])
    return machine,states


class Tests(unittest.TestCase):
    def equivalent(self, actual, expected):
        solver=z3.Solver();solver.add(actual != expected)
        self.assertEqual(solver.check(),z3.unsat)

    def test_result_block_keeps_outer_operand(self):
        _,states=run(bytes.fromhex('42 05 02 7e 42 07 0c 00 42 08 0b 7c 0b'))
        self.equivalent(states[0].stack[0].bits,12)

    def test_branch_crosses_inner_label(self):
        _,states=run(bytes.fromhex('42 05 02 7e 02 40 42 09 0c 01 0b 42 08 0b 7c 0b'))
        self.equivalent(states[0].stack[0].bits,14)

    def test_if_result_and_coverage(self):
        x=z3.BitVec('condition',32)
        _,states=run(bytes.fromhex('20 00 04 7e 42 01 05 42 02 0b 0b'),[Value('i32',x)],b'\x7f')
        self.assertEqual(len(states),2)
        for state in states:
            solver=z3.Solver();solver.add(state.condition,state.stack[0].bits != z3.If(x!=0,z3.BitVecVal(1,64),z3.BitVecVal(2,64)))
            self.assertEqual(solver.check(),z3.unsat)

    def test_implicit_function_branch(self):
        _,states=run(bytes.fromhex('42 09 0c 00 42 03 0b'))
        self.equivalent(states[0].stack[0].bits,9)

    def test_shift_count_is_masked(self):
        # 65 encoded as signed LEB; WASM i64.shl masks to one bit.
        _,states=run(bytes.fromhex('42 01 42 c1 00 86 0b'))
        self.equivalent(states[0].stack[0].bits,2)

    def test_signed_unsigned_shift(self):
        for opcode,expected in [(0x87,(1<<64)-1),(0x88,(1<<63)-1)]:
            _,states=run(bytes.fromhex('42 7f 42 01')+bytes([opcode,0x0b]))
            self.equivalent(states[0].stack[0].bits,expected)

    def test_clz_zero_and_high_bit(self):
        for width in [32,64]:
            for number,expected in [(0,width),(1,width-1),(1<<(width-1),0)]:
                self.equivalent(clz(z3.BitVecVal(number,width)),expected)

    def test_unaligned_little_endian_store_load(self):
        _,states=run(bytes.fromhex('41 03 42 25 37 00 00 41 03 29 00 00 0b'))
        self.equivalent(states[0].stack[0].bits,37)
        self.equivalent(z3.Select(states[0].memory,z3.BitVecVal(3,32)),37)
        self.equivalent(z3.Select(states[0].memory,z3.BitVecVal(4,32)),0)

    def test_effective_address_does_not_wrap(self):
        machine,_=run(bytes.fromhex('41 78 29 00 08 0b'))
        self.assertTrue(z3.is_false(z3.simplify(machine.accesses[0][1])))

    def test_fail_closed(self):
        for body in [bytes.fromhex('00 0b'),bytes.fromhex('03 40 0b 0b'),bytes.fromhex('7c 0b'),
                     bytes.fromhex('10 01 0b'),bytes.fromhex('41 01 0b')]:
            with self.assertRaises((Unsupported,IndexError)):
                run(body)

    def test_unknown_feasibility_is_error(self):
        machine=Machine(module(bytes.fromhex('42 00 0b')),z3.BoolVal(True),65536,{0})
        with patch('machine.z3.Solver') as solver:
            solver.return_value.check.return_value=z3.unknown
            solver.return_value.reason_unknown.return_value='injected timeout'
            with self.assertRaisesRegex(Unsupported,'Unknown path feasibility'):
                machine.possible(z3.Bool('unknown_path'))


if __name__=='__main__': unittest.main()
