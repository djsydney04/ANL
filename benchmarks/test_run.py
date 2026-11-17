"""The benchmark must reject fast, wrong output instead of reporting it as speed."""

import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("apl_benchmark", Path(__file__).with_name("run.py"))
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


class SemanticGateTests(unittest.TestCase):
    def test_correct_value_and_expected_trap_are_accepted(self):
        benchmark.validate({"exit": 0, "stdout": "42\n", "stderr": ""}, {"exit": 0, "stdout": "42\n"}, "value")
        benchmark.validate({"exit": 2, "stdout": "", "stderr": "division_by_zero"},
                           {"exit": 2, "stdout": "", "stderr_contains": "division_by_zero"}, "trap")

    def test_wrong_result_fast_rejection_and_wrong_trap_cannot_be_measured(self):
        expected_value = {"exit": 0, "stdout": "42\n"}
        expected_trap = {"exit": 2, "stdout": "", "stderr_contains": "division_by_zero"}
        for observed, expected in [
            ({"exit": 0, "stdout": "41\n", "stderr": ""}, expected_value),
            ({"exit": 1, "stdout": "", "stderr": "syntax error"}, expected_value),
            ({"exit": 0, "stdout": "42\n", "stderr": "warning"}, expected_value),
            ({"exit": 2, "stdout": "", "stderr": "arithmetic_overflow"}, expected_trap),
            ({"exit": 2, "stdout": "", "stderr": ""}, expected_trap),
            ({"exit": 2, "stdout": "42\n", "stderr": "division_by_zero"}, expected_trap),
        ]:
            with self.subTest(observed=observed), self.assertRaises(benchmark.SemanticFailure):
                benchmark.validate(observed, expected, "injected defect")


if __name__ == "__main__":
    unittest.main()
