"""Regression checks for source identity and required validation receipts."""

from contextlib import redirect_stdout
import io
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import verify_evidence


class EvidenceChecksTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="levi-civita-evidence-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        source = verify_evidence.ROOT
        for directory in ["MathlibExtensions", "LeviCivitaSmoothness", "evidence"]:
            shutil.copytree(source / directory, self.root / directory)
        for name in ["MathlibExtensions.lean", "LeviCivitaSmoothness.lean", "lean-toolchain"]:
            shutil.copyfile(source / name, self.root / name)

    def check_evidence(self):
        with patch.object(verify_evidence, "ROOT", self.root), redirect_stdout(io.StringIO()):
            verify_evidence.main()

    def test_current_evidence_passes(self):
        self.check_evidence()

    def test_each_validation_receipt_is_required(self):
        for name in ["validation.json", "hom-validation.json", "lint-validation.json"]:
            with self.subTest(receipt=name):
                receipt = self.root / "evidence" / name
                saved = receipt.with_suffix(".saved")
                receipt.rename(saved)
                try:
                    with self.assertRaises(FileNotFoundError) as failure:
                        self.check_evidence()
                    self.assertIn("Required validation receipt missing", str(failure.exception))
                    self.assertIn(name, str(failure.exception))
                finally:
                    saved.rename(receipt)

    def test_missing_receipts_cannot_hide_hom_source_drift(self):
        for name in ["hom-validation.json", "lint-validation.json"]:
            receipt = self.root / "evidence" / name
            receipt.rename(receipt.with_suffix(".saved"))
        source = self.root / "LeviCivitaSmoothness/HomRecovery.lean"
        source.write_text(source.read_text() + "\n-- Changed after the recorded checks.\n")
        with self.assertRaises(FileNotFoundError):
            self.check_evidence()

    def test_present_receipts_reject_hom_source_drift(self):
        source = self.root / "LeviCivitaSmoothness/HomRecovery.lean"
        source.write_text(source.read_text() + "\n-- Changed after the recorded checks.\n")
        with self.assertRaises(AssertionError) as failure:
            self.check_evidence()
        self.assertIn("LeviCivitaSmoothness/HomRecovery.lean", str(failure.exception))


if __name__ == "__main__":
    unittest.main()
