"""GPL-2.0-or-later. Failure-path checks for the verification orchestration."""
import os
import subprocess
import sys
import unittest
from source import HERE, ROOT
from kernel_tools import require_success, require_rejection


class RunnerTests(unittest.TestCase):
    def test_success(self):
        require_success(0, "'checked' depends on axioms: [propext]\n")

    def test_nonzero_and_logged_failures(self):
        for code, output in [(1, ''), (0, 'PANIC: recovered'), (0, 'error: rejected'),
          (0, 'declaration uses sorry'), (0, 'sorryAx')]:
            with self.subTest(code=code, output=output), self.assertRaises(RuntimeError):
                require_success(code, output)

    def test_expected_mutation_failure(self):
        require_rejection(1, 'error: Type mismatch at x + y', ('Type mismatch', 'x + y'))

    def test_mutation_wrong_failure(self):
        for code, output in [(0, 'Type mismatch'), (1, 'missing import'),
          (1, 'PANIC: Type mismatch'), (0, 'PANIC: Type mismatch')]:
            with self.subTest(code=code, output=output), self.assertRaises(RuntimeError):
                require_rejection(code, output, ('Type mismatch',))

    def test_optimized_python_rejected_before_work(self):
        for name in ['source.py', 'check.py', 'run.py', 'kernel_negatives.py']:
            process = subprocess.run([sys.executable, '-O', str(HERE / name)], cwd=ROOT,
              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
            with self.subTest(source=name):
                self.assertNotEqual(process.returncode, 0)
                self.assertIn('Optimized Python is forbidden', process.stdout)

    def test_optimization_environment_rejected(self):
        process = subprocess.run([sys.executable, str(HERE / 'run.py'), '--certificates-only'],
          cwd=ROOT, env={**os.environ, 'PYTHONOPTIMIZE': '1'}, text=True,
          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertNotEqual(process.returncode, 0)
        self.assertIn('Optimized Python is forbidden', process.stdout)


if __name__ == '__main__':
    unittest.main()
