# Documentation and full-source lint checkpoint

This checkpoint starts at `270e6d9`. The mathematical proofs are unchanged. For each of
`KoszulTransfer.lean`, `MathlibBridge.lean`, `MetricApplication.lean`, and `HomRecovery.lean`,
removing the newly added copyright header and, in `MathlibBridge.lean`, the new theorem
docstring reproduces the previous file byte for byte. Every one of the original 19 extracted
files still matches its source-manifest SHA-256 (5,037 lines total).

The two import roots and two axiom-audit files gained module documentation and copyright
headers. The long source-theorem reference in `AxiomAudit.lean` uses an opened namespace to
remain below 100 characters; the refreshed audit resolves the same fully qualified declaration.

## Executed checks

The strict `lake --rehash --wfail build` gate passed for both library roots, `HomRecovery`,
and both axiom-audit modules. The probes again report only `propext`, `Classical.choice`,
and `Quot.sound`.

Each of these eight full source files was independently re-elaborated with its original
project-relative module identity and `#lint+ docBlame docBlameThm` appended:

* `LeviCivitaSmoothness/KoszulTransfer.lean`
* `LeviCivitaSmoothness/MathlibBridge.lean`
* `LeviCivitaSmoothness/MetricApplication.lean`
* `LeviCivitaSmoothness/HomRecovery.lean`
* `LeviCivitaSmoothness/AxiomAudit.lean`
* `LeviCivitaSmoothness/HomAxiomAudit.lean`
* `LeviCivitaSmoothness.lean`
* `MathlibExtensions.lean`

Every file reported zero errors with 16 environment linters. The verbose logs record declaration
type checking, definition naming, deprecation dates, definition and theorem documentation,
instance checks, simp checks, propositional structures, declaration names, tautologies, tactic
documentation/naming, unused arguments, and unused term-mode `have` statements. Slow default
environment linters were included. Import roots and audit-only modules may have no declarations
of their own; the mathematical proof sources were re-elaborated in full rather than merely
imported into an empty lint module.

The commands had the form:

```sh
lake env lean -j2 --json --root=<probe-root> <probe-root>/<original-relative-source>
```

They ran sequentially under the qualified resource guard. Diagnostics had to be valid clean JSON,
and each result had to contain both the lint-success marker and `with 16 linters`. Source and
probe hashes were checked before execution, and source hashes were checked again afterward.
The exact executed probes are archived as `.lean.txt` evidence snapshots.

## Mechanical syntax/style scope

The recorded `verify-mathlib-bar.sh` mechanical checks passed for all eight files: copyright and module
headers, coercion spelling, focused imports, proof blank lines, line lengths, standalone `by`,
lambda syntax, and dollar application. The owning repository's commit-history check was also
performed separately. This is the mechanical set used by that verifier; Mathlib's entire
optional `linter.mathlibStandardSet` was not enabled or claimed.

`evidence/lint-validation.json` records all eight source/probe/log hashes, per-file results,
mechanical-check evidence, and the guarded strict/lint receipts. The original extracted cone's
separate strict-build/hash certificate remains intact; this lint certificate covers the eight
new files, not a fresh full-source lint of every imported file.
