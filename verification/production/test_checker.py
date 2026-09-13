#!/usr/bin/env python3
"""GPL-2.0-or-later. Regressions for the production checker's rejection boundary."""
import json
import sys
import unittest
from pathlib import Path
from decoder import Op, Reader, Unsupported, Module, decode, function, locate_slice
from machine import Affine, Graph, IntParam, Machine, Memory, Ptr

ROOT=Path(__file__).resolve().parents[2]
SHIPPED=Path(sys.argv[1]) if __name__=='__main__' and len(sys.argv)==2 else ROOT/'dist/fo.wasm'


def op(name,*args,body=None):
    return Op(name,args,0,1,body,[] if body is not None else None)


class BoundaryTests(unittest.TestCase):
    def setUp(self):
        self.graph=Graph()
        self.memory=Memory(self.graph,{'output':(0,16),'coefficient':(0,384)})
        self.machine=Machine(self.graph,self.memory,{},self.graph.symbol('tc'),True)

    def test_unknown_raw_opcode(self):
        with self.assertRaises(Unsupported):decode(Reader(b'\xfd\x00\x0b',0))

    def test_escaped_branch(self):
        with self.assertRaisesRegex(Unsupported,'escapes'):self.machine.execute([op('br',0)])

    def test_uninitialized_local(self):
        with self.assertRaisesRegex(Unsupported,'Uninitialized'):self.machine.execute([op('local.get',7),op('drop')])

    def test_uninitialized_memory(self):
        with self.assertRaisesRegex(Unsupported,'Uninitialized'):self.memory.get(Ptr('output'),'f64')

    def test_wrong_access_type(self):
        self.memory.put(Ptr('output'),'f64',self.graph.literal(1),True)
        with self.assertRaisesRegex(Unsupported,'type-punned'):self.memory.get(Ptr('output'),'i32')

    def test_partial_alias_write(self):
        self.memory.put(Ptr('output'),'f64',self.graph.literal(1),True)
        with self.assertRaisesRegex(Unsupported,'Overlapping'):self.memory.put(Ptr('output',4),'i32',0)

    def test_coefficient_write(self):
        self.memory.readonly.add('coefficient')
        with self.assertRaisesRegex(Unsupported,'Write to coefficient'):self.memory.put(Ptr('coefficient'),'f64',self.graph.literal(0))

    def test_output_bounds_and_alignment(self):
        for offset in (-8,1,16):
            with self.subTest(offset=offset), self.assertRaises(Unsupported):
                self.memory.put(Ptr('output',offset),'f64',self.graph.literal(0))

    def test_affine_access_cannot_leave_subinterval(self):
        self.memory.coefficient_stride=48
        self.assertIsNotNone(self.memory.get(Ptr('coefficient',Affine(48,40)),'f64'))
        # Address still lies in the overall buffer for a smaller slope; the
        # per-subinterval contract must reject it independently of that bound.
        for offset in (Affine(40,40),Affine(40,48),Affine(48,-8)):
            with self.subTest(offset=offset), self.assertRaises(Unsupported):
                self.memory.get(Ptr('coefficient',offset),'f64')

    def test_affine_integer_overflow(self):
        self.machine.locals[0]=Affine(1)
        with self.assertRaisesRegex(Unsupported,'may wrap'):
            self.machine.execute([op('local.get',0),op('i32.const',1<<30),op('i32.mul'),op('drop')])

    def test_unknown_symbolic_zero_branch(self):
        self.machine.locals[0]=IntParam('arbitrary')
        with self.assertRaisesRegex(Unsupported,'Unproved'):
            self.machine.execute([op('local.get',0),op('i32.eqz'),op('drop')])

    def test_unknown_symbolic_select(self):
        self.machine.locals[0]=IntParam('arbitrary')
        with self.assertRaisesRegex(Unsupported,'Nonconcrete select'):
            self.machine.execute([op('i32.const',1),op('i32.const',2),op('local.get',0),op('select'),op('drop')])

    def test_unproved_floating_branch(self):
        with self.assertRaisesRegex(Unsupported,'Unproved floating'):
            self.machine.fp_compare('f64.eq',self.graph.symbol('a'),self.graph.symbol('b'))

    def test_loop_limit(self):
        with self.assertRaisesRegex(Unsupported,'Loop bound'):
            self.machine.execute([op('loop',body=[op('br',0)])])

    def test_stack_result_mismatch(self):
        with self.assertRaisesRegex(Unsupported,'stack mismatch'):
            self.machine.execute([op('block',body=[op('i32.const',1)])])

    def test_no_unproved_fp_rewrites(self):
        a,b,c=[self.graph.symbol(x) for x in 'abc'];f=self.graph.operation
        self.assertNotEqual(self.graph.literal(0),self.graph.literal(-0.0))
        self.assertNotEqual(f('add',f('add',a,b),c),f('add',a,f('add',b,c)))
        self.assertNotEqual(f('add',a,self.graph.literal(0)),a)
        self.assertNotEqual(f('sub',a,b),f('sub',b,a))
        self.assertEqual(f('mul',a,b),f('mul',b,a))

    def test_ambiguous_actual_cfg_rejected(self):
        module=Module(SHIPPED.read_bytes())
        _,_,_,ops=function(module,module.locate('jpl_state'))
        locate_slice(ops)
        with self.assertRaisesRegex(Unsupported,'found 2'):locate_slice(ops+ops)


if __name__=='__main__':
    if sys.flags.optimize:raise RuntimeError('Optimized Python forbidden')
    result=unittest.TextTestRunner(stream=sys.stderr,verbosity=1).run(unittest.defaultTestLoader.loadTestsFromTestCase(BoundaryTests))
    print(json.dumps({'passed':result.wasSuccessful(),'tests':result.testsRun,'failures':len(result.failures),'errors':len(result.errors)}))
    sys.exit(0 if result.wasSuccessful() else 1)
