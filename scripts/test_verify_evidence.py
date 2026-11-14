"""Regression checks for source identity and required validation receipts."""

from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import shutil
import tempfile
import subprocess
import sys
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

    def test_present_receipts_reject_historical_hom_snapshot_drift(self):
        mapping = json.loads((self.root / 'evidence/historical-sources.json').read_text())
        source = self.root / mapping['source_snapshots'][
            'LeviCivitaSmoothness/HomRecovery.lean']['snapshot']
        source.write_text(source.read_text() + "\n-- Changed after the recorded checks.\n")
        with self.assertRaises(AssertionError) as failure:
            self.check_evidence()
        self.assertIn("LeviCivitaSmoothness/HomRecovery.lean", str(failure.exception))

    def test_current_port_source_changes_are_not_rebound_to_old_receipts(self):
        source = self.root / 'LeviCivitaSmoothness/HomRecovery.lean'
        source.write_text(source.read_text() + '\n-- Current source documentation.\n')
        self.check_evidence()

    def test_missing_historical_snapshot_fails(self):
        mapping = json.loads((self.root / 'evidence/historical-sources.json').read_text())
        (self.root / mapping['source_snapshots'][
            'LeviCivitaSmoothness/HomRecovery.lean']['snapshot']).unlink()
        with self.assertRaises(FileNotFoundError):
            self.check_evidence()

    def test_original_receipt_and_log_bytes_cannot_be_rewritten(self):
        for relative in ['evidence/validation.json', 'evidence/builds/exact-core.log']:
            with self.subTest(relative=relative):
                path = self.root / relative
                original = path.read_bytes()
                path.write_bytes(original + b'\n')
                try:
                    with self.assertRaises(AssertionError):
                        self.check_evidence()
                finally:
                    path.write_bytes(original)

    def test_historical_sdk_pin_mismatch_fails(self):
        path = self.root / 'evidence/historical-sources.json'
        mapping = json.loads(path.read_text())
        mapping['toolchain'] = 'leanprover/lean4:v4.35.0'
        path.write_text(json.dumps(mapping))
        with self.assertRaises(AssertionError):
            self.check_evidence()

    def test_current_entry_root_trust_marker_is_scanned(self):
        path = self.root / 'LeviCivitaSmoothness.lean'
        path.write_text(path.read_text() + '\naxiom untrusted : False\n')
        with self.assertRaises(AssertionError):
            self.check_evidence()

    def test_optimized_python_refused(self):
        result = subprocess.run([sys.executable, '-O', str(Path(verify_evidence.__file__)),
                                 '--help'], text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('requires enabled Python assertions', result.stderr)


if __name__ == "__main__":
    unittest.main()
