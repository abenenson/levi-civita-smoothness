"""Fail-closed controls for the live lint and axiom diagnostics, without running Lean."""

import json
import unittest

import verify_live


class LiveDiagnosticsTests(unittest.TestCase):
    def historical_output(self, relative):
        name = relative.replace("/", "-") + ".log"
        return (verify_live.ROOT / "evidence/full-lint/logs" / name).read_text()

    def test_all_eight_recorded_outputs_pass(self):
        for relative in verify_live.LINT_SOURCES:
            with self.subTest(source=relative):
                verify_live.check_diagnostics(self.historical_output(relative),
                                              verify_live.ROOT / relative)

    def test_missing_lint_result_fails(self):
        with self.assertRaises(AssertionError):
            verify_live.check_diagnostics("", verify_live.ROOT / "MathlibExtensions.lean")

    def test_warning_fails(self):
        relative = "MathlibExtensions.lean"
        output = self.historical_output(relative)
        output += json.dumps({"severity": "warning", "data": "unexpected warning"}) + "\n"
        with self.assertRaises(AssertionError):
            verify_live.check_diagnostics(output, verify_live.ROOT / relative)

    def test_missing_sixteen_linter_marker_fails(self):
        relative = "MathlibExtensions.lean"
        output = self.historical_output(relative).replace("with 16 linters", "with 15 linters")
        with self.assertRaises(AssertionError):
            verify_live.check_diagnostics(output, verify_live.ROOT / relative)

    def test_missing_axiom_record_fails(self):
        relative = "LeviCivitaSmoothness/HomAxiomAudit.lean"
        output = self.historical_output(relative).splitlines()[1:]
        with self.assertRaises(AssertionError):
            verify_live.check_diagnostics("\n".join(output), verify_live.ROOT / relative)

    def test_unexpected_axiom_fails(self):
        relative = "LeviCivitaSmoothness/HomAxiomAudit.lean"
        output = self.historical_output(relative).replace("Quot.sound", "sorryAx")
        with self.assertRaises(AssertionError):
            verify_live.check_diagnostics(output, verify_live.ROOT / relative)

    def test_wrong_theorem_fails(self):
        relative = "LeviCivitaSmoothness/HomAxiomAudit.lean"
        output = self.historical_output(relative).replace(
            "LeviCivitaSmoothness.contMDiff_hom_of_smooth_apply", "Unrelated.theorem")
        with self.assertRaises(AssertionError):
            verify_live.check_diagnostics(output, verify_live.ROOT / relative)

    def test_malformed_json_fails(self):
        with self.assertRaises(json.JSONDecodeError):
            verify_live.check_diagnostics("not JSON", verify_live.ROOT / "MathlibExtensions.lean")

    def test_every_manifest_and_lint_source_is_a_strict_target(self):
        manifest = json.loads((verify_live.ROOT / "evidence/source-manifest.json").read_text())
        expected = {item["destination"] for item in manifest["files"]}
        expected.update(verify_live.LINT_SOURCES)
        actual = {str(path.relative_to(verify_live.ROOT))
                  for path in verify_live.authored_sources()}
        self.assertEqual(actual, expected)
        self.assertEqual(len(actual), 27)


if __name__ == "__main__":
    unittest.main()
