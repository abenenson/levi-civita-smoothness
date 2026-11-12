#!/usr/bin/env python3
"""Rebuild every authored module and repeat the eight full-source lint/axiom probes."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

from verify_evidence import ROOT, lean_code

ARTIFACTS = ROOT / "verification-artifacts"
LINT_IMPORT = "Mathlib.Tactic.Linter.Lint"
LINT_SOURCES = (
    "LeviCivitaSmoothness/KoszulTransfer.lean",
    "LeviCivitaSmoothness/MathlibBridge.lean",
    "LeviCivitaSmoothness/MetricApplication.lean",
    "LeviCivitaSmoothness/HomRecovery.lean",
    "LeviCivitaSmoothness/AxiomAudit.lean",
    "LeviCivitaSmoothness/HomAxiomAudit.lean",
    "LeviCivitaSmoothness.lean",
    "MathlibExtensions.lean",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_THEOREMS = {
    "LeviCivitaSmoothness/AxiomAudit.lean": (
        "MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothTangentSection."
        "exists_leviCivitaTangentConnectionFromMetric",
        "LeviCivitaSmoothness.eq_covDerivFromMetric_of_koszul",
        "LeviCivitaSmoothness.leviCivitaConnection_eq_covDerivFromMetric",
        "LeviCivitaSmoothness.contMDiff_leviCivitaConnection_smooth_pair",
        "LeviCivitaSmoothness.contMDiff_leviCivitaConnection_fromMetric",
    ),
    "LeviCivitaSmoothness/HomAxiomAudit.lean": (
        "LeviCivitaSmoothness.contMDiff_hom_of_smooth_apply",
        "LeviCivitaSmoothness.contMDiffCovariantDerivative_leviCivitaConnection",
        "LeviCivitaSmoothness.contMDiffCovariantDerivative_leviCivitaConnection_fromMetric",
    ),
}


def authored_sources():
    sources = [ROOT / "MathlibExtensions.lean", ROOT / "LeviCivitaSmoothness.lean"]
    for directory in ("MathlibExtensions", "LeviCivitaSmoothness"):
        sources.extend(sorted((ROOT / directory).rglob("*.lean")))
    return sources


def cache_imports():
    modules = {LINT_IMPORT}
    for source in authored_sources():
        modules.update(re.findall(r"^import\s+(Mathlib\.\S+)",
                                  lean_code(source.read_text()), re.M))
    return sorted(modules)


def cache_command():
    """Resolve focused imports through Lake's module search path."""
    return ["lake", "exe", "cache", "get", *cache_imports()]


def check_diagnostics(output, source):
    messages = [json.loads(line) for line in output.splitlines() if line.strip()]
    assert messages, f"No Lean diagnostics: {source}"
    for message in messages:
        assert message["severity"] == "information", message
    data = [message["data"] for message in messages]
    assert any("All linting checks passed!" in text
               and "Found 0 errors" in text
               and "with 16 linters" in text for text in data), source
    expected = AXIOM_THEOREMS.get(str(source.relative_to(ROOT)), ())
    actual = []
    for text in data:
        match = re.fullmatch(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S)
        if match:
            actual.append(match[1])
            axioms = {name.strip() for name in match[2].split(",") if name.strip()}
            assert axioms <= STANDARD_AXIOMS, (match[1], axioms)
    assert tuple(actual) == expected, (source, expected, actual)


def run(command, log):
    print("+ " + " ".join(command), flush=True)
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    log.write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    return result.stdout


def verify():
    ARTIFACTS.mkdir(exist_ok=True)
    sources = authored_sources()
    targets = ["+" + str(source.relative_to(ROOT).with_suffix("")).replace("/", ".")
               + ":olean" for source in sources]
    # Explicit targets include all 19 construction files, even if an import root changes.
    run(["lake", "--rehash", "--wfail", "build", *targets], ARTIFACTS / "strict-build.log")
    with tempfile.TemporaryDirectory(prefix="levi-civita-lint-") as temporary:
        probe_root = Path(temporary)
        for relative in LINT_SOURCES:
            source = ROOT / relative
            original = source.read_bytes()
            probe = probe_root / relative
            probe.parent.mkdir(parents=True, exist_ok=True)
            probe.write_text(f"import {LINT_IMPORT}\n" + original.decode()
                             + "\n#lint+ docBlame docBlameThm\n")
            output = run(["lake", "env", "lean", "-j2", "--json",
                          f"--root={probe_root}", str(probe)],
                         ARTIFACTS / (relative.replace("/", "-") + ".jsonl"))
            check_diagnostics(output, source)
            assert source.read_bytes() == original, f"Source changed during lint: {relative}"
    print(f"Verified {len(sources)} strict authored targets and {len(LINT_SOURCES)} "
          "full-source probes with 16 linters; all eight axiom probes passed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", action="store_true",
                        help="fetch only the Mathlib import closure needed by these checks")
    args = parser.parse_args()
    if args.cache:
        # Module names resolve inside the pinned Mathlib package through Lake's search path.
        subprocess.run(cache_command(), cwd=ROOT, check=True)
    else:
        verify()
