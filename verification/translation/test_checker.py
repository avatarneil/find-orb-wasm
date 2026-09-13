"""Regression controls for the trusted checker: reject unsound shortcuts."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import z3
from model import Memory, Pointer, Unsupported, F64, ZERO
from verify import congruence_abstraction, sqrt_zero_rewrite, Obligations

class CheckerTests(unittest.TestCase):
    def test_signed_zero_is_observable(self):
        self.assertTrue(z3.is_true(z3.simplify(ZERO != z3.fpMinusZero(F64))))

    def test_nan_payloads_are_explicitly_quotiented(self):
        self.assertTrue(z3.is_true(z3.simplify(z3.fpNaN(F64) == z3.fpNaN(F64))))

    def test_no_type_punning(self):
        memory=Memory();memory.store(Pointer('a'), 'f64', ZERO)
        with self.assertRaises(Unsupported):memory.load(Pointer('a'), 'i32')

    def test_no_out_of_bounds(self):
        memory=Memory()
        for offset in [-8,24,32]:
            with self.assertRaises(Unsupported):memory.store(Pointer('a',offset),'f64',ZERO)

    def test_no_symbolic_address(self):
        with self.assertRaises(Unsupported):Pointer('a').add(z3.Int('index'))

    def test_no_readonly_writes(self):
        memory=Memory();memory.readonly.add('a')
        with self.assertRaises(Unsupported):memory.store(Pointer('a'),'f64',ZERO)

    def test_no_uninitialized_read(self):
        with self.assertRaises(Unsupported):Memory().load(Pointer('a'),'f64')

    def test_abstraction_preserves_distinct_operations(self):
        x,y=z3.FPs('x y',F64)
        concrete=z3.fpAdd(z3.RNE(),x,y)!=z3.fpSub(z3.RNE(),x,y)
        abstract,mapping=congruence_abstraction(concrete)
        self.assertEqual(len(mapping),2)
        solver=z3.Solver();solver.add(abstract)
        self.assertEqual(solver.check(),z3.sat)

    def test_rewrite_only_proven_zero_lemma(self):
        x=z3.FP('x',F64);root=z3.fpSqrt(z3.RNE(),x)
        self.assertTrue(sqrt_zero_rewrite(z3.fpEQ(root,ZERO)).eq(z3.fpEQ(x,ZERO)))
        untouched=z3.fpEQ(root,z3.FPVal(1,F64))
        self.assertTrue(sqrt_zero_rewrite(untouched).eq(untouched))

    def test_unknown_cannot_pass(self):
        solver=z3.Solver()
        with tempfile.TemporaryDirectory() as temp:
            with patch.object(solver,'check',return_value=z3.unknown):
                with patch('verify.z3.Solver',return_value=solver):
                    with self.assertRaises(AssertionError):
                        Obligations(Path(temp)).check('unknown',z3.BoolVal(False))

if __name__=='__main__':unittest.main()
