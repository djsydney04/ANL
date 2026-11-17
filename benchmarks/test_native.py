"""A native baseline retains failed observations and rejects changed inputs."""

import sys
import unittest

import native


class NativeEvidenceTests(unittest.TestCase):
    def test_wrong_value_is_rejected_and_retained(self):
        report = {"invocations": []}
        with self.assertRaises(native.SemanticFailure):
            native.record(report, [sys.executable, "-c", "print(41)"],
                          {"exit": 0, "stdout": "42\n"}, "wrong executable", 5)
        self.assertEqual(report["invocations"][0]["stdout"], "41\n")
        self.assertEqual(report["invocations"][0]["exit"], 0)
        self.assertIn("wrong stdout", report["invocations"][0]["failure"])

    def test_timeout_is_rejected_and_retained(self):
        report = {"invocations": []}
        with self.assertRaises(native.SemanticFailure):
            native.record(report, [sys.executable, "-c", "import time; time.sleep(5)"],
                          {"exit": 0}, "stalled executable", 0.02)
        self.assertIn("exceeded", report["invocations"][0]["failure"])

    def test_source_changes_and_additions_invalidate_measurements(self):
        for observed in ({"a.rs": "changed"}, {"a.rs": "same", "b.rs": "added"}, {}):
            with self.subTest(observed=observed), self.assertRaises(native.SemanticFailure):
                native.require_same({"a.rs": "same"}, observed, "compiler inputs")


if __name__ == "__main__":
    unittest.main()
