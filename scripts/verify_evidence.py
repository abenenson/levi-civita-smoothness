#!/usr/bin/env python3
"""Verify immutable source evidence without invoking Lean or accessing the network."""

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def lean_code(text):
    """Remove nested comments and string contents before checking trust markers."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i : i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    assert not depth, "unclosed block comment"
    assert not string, "unclosed string"
    return "".join(out)


def main():
    manifest = json.loads((ROOT / "evidence/source-manifest.json").read_text())
    for item in manifest["files"]:
        data = (ROOT / item["destination"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == item["sha256"], item["destination"]
        assert len(data.splitlines()) == item["lines"], item["destination"]
    provenance = json.loads((ROOT / "evidence/provenance.json").read_text())
    for item in provenance["files"]:
        data = (ROOT / item["snapshot"]).read_bytes()
        obj = b"blob " + str(len(data)).encode() + b"\0" + data
        assert hashlib.sha1(obj).hexdigest() == item["blob_sha"], item["snapshot"]
    files = sorted((ROOT / "MathlibExtensions").rglob("*.lean"))
    files += sorted((ROOT / "LeviCivitaSmoothness").rglob("*.lean"))
    for path in files:
        code = lean_code(path.read_text())
        assert not re.search(r"\b(sorry|admit|axiom)\b", code), str(path)
        assert not re.search(r"set_option\s+debug\.skipKernelTC\s+true", code), str(path)
        for module in re.findall(r"^import\s+(MathlibExtensions\S+|LeviCivitaSmoothness\S+)", code, re.M):
            target = ROOT / (module.replace(".", "/") + ".lean")
            assert target.is_file(), f"missing import: {module}"
    assert (ROOT / "lean-toolchain").read_text().strip() == provenance["package"]["toolchain"]
    for name in ["validation.json", "hom-validation.json", "lint-validation.json"]:
        validation_path = ROOT / "evidence" / name
        if not validation_path.is_file():
            raise FileNotFoundError(f"Required validation receipt missing: evidence/{name}")
        validation = json.loads(validation_path.read_text())
        for path, expected in validation["new_proof_source_hashes"].items():
            assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path
        for phase in validation["phases"]:
            assert phase["exit_code"] == 0 and phase["reason"] == "completed", phase["name"]
            log = (ROOT / phase["log"]).read_bytes()
            assert hashlib.sha256(log).hexdigest() == phase["log_sha256"], phase["log"]
            receipt = json.loads((ROOT / phase["resource_receipt"]).read_text())
            assert receipt["exit_code"] == 0 and receipt["reason"] == "completed", phase["name"]
        if "file_results" in validation:
            assert {x["source"] for x in validation["file_results"]} == set(
                validation["new_proof_source_hashes"])
            for item in validation["file_results"]:
                assert item["status"] == "passed" and item["exit_code"] == 0, item["source"]
                assert item["environment_linter_count"] == 16, item["source"]
                for path_key, hash_key in [("log", "log_sha256"),
                                           ("probe_snapshot", "probe_sha256")]:
                    data = (ROOT / item[path_key]).read_bytes()
                    assert hashlib.sha256(data).hexdigest() == item[hash_key], item[path_key]
    print(json.dumps({
        "source_files_verified": len(manifest["files"]),
        "source_lines_verified": sum(x["lines"] for x in manifest["files"]),
        "upstream_snapshots_verified": len(provenance["files"]),
        "lean_files_scanned": len(files),
        "forbidden_trust_markers": 0,
        "this_check_invokes_lean": False,
    }, indent=2))


if __name__ == "__main__":
    main()
