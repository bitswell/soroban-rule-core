#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""Self-tests for tools/check-claims.

Each ledger in tools/tests/ledgers/ is checked against the fixture repository
in tools/tests/fixture/, with the fixture's test list standing in for cargo.
`pass.yaml` must pass. Every other ledger must fail, reporting exactly the
problems its `# expect:` lines name, one problem per line.
"""

import contextlib
import importlib.machinery
import importlib.util
import io
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixture"
LEDGERS = HERE / "ledgers"

# Load the checker without leaving its bytecode in tools/.
sys.dont_write_bytecode = True
loader = importlib.machinery.SourceFileLoader("check_claims", str(HERE.parent / "check-claims"))
spec = importlib.util.spec_from_loader("check_claims", loader)
check_claims = importlib.util.module_from_spec(spec)
loader.exec_module(check_claims)


def run(ledger: Path) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    argv = ["--root", str(FIXTURE), "--ledger", str(ledger), "--test-list", str(FIXTURE / "tests.txt")]
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = check_claims.main(argv)
    return code, out.getvalue(), err.getvalue()


class Ledgers(unittest.TestCase):
    def test_pass(self):
        code, out, err = run(LEDGERS / "pass.yaml")
        self.assertEqual(err, "")
        self.assertEqual(code, 0)
        self.assertIn("6 claims, evidence present", out)

    def test_each_defect_is_reported(self):
        failing = sorted(p for p in LEDGERS.glob("*.yaml") if p.name != "pass.yaml")
        self.assertGreater(len(failing), 0)
        for ledger in failing:
            with self.subTest(ledger=ledger.name):
                expected = re.findall(r"^# expect: (.+)$", ledger.read_text(), re.M)
                self.assertTrue(expected, "a failing ledger names what it expects")
                code, out, err = run(ledger)
                self.assertEqual(code, 1)
                self.assertEqual(out, "")
                problems = [line for line in err.splitlines() if line.startswith(str(ledger))]
                self.assertEqual(len(problems), len(expected), err)
                for want in expected:
                    self.assertTrue(any(want in p for p in problems), f"{want!r} not in:\n{err}")


class Record(unittest.TestCase):
    def test_reads_only_the_record(self):
        self.assertEqual(
            check_claims.record_theorems(FIXTURE),
            {"Fixture.narrower_trans", "Fixture.allows_eq"},
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
