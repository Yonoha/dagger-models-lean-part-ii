# Saved local Theorem C verification

This AI-assisted record distinguishes the original local proof from new-repository
checks. Independent human correspondence review is pending.

## Original proof evidence

- [Summary](summary.json): original four-link target, original hypotheses,
  universe-zero scope and dependency pins.
- [Project source gate](project-source-gate.json): all 156 directly imported
  project roots passed Lake content rehash/no-build, covering the transitive
  project source graph. No compilation was performed by that freshness gate.
- [359 stage receipts and axiom logs](stages/): actual successful kernel builds,
  unchanged source/import hashes and 1,182 standard printed axiom reports.
- [Main theorem axiom log](stages/TheoremCOriginalCompletionProof.log) and
  [four literal target axiom log](stages/TheoremCOriginalFourLinksAudit.log).

The public JSON receipts are normalized exports, with private machine paths and
commands removed. Each records the SHA-256 of its original receipt. The actual
Lean source and axiom-log bytes are unchanged. The wider original development
contained 473 checked stages and 1,712 printed standard axiom reports; unused
intermediate stages from that wider set are not added to this proof closure.

The original final proof and four-link audit were also recompiled from a saved
source snapshot. That did not rebuild all their dependencies. The original
statement, raw comparison and Part II manuscript hashes were retained.

## Separate repository checks

The source inventory is checked by `scripts/verify_snapshot.py`, including the
exact final target names and saved transitive axiom reports. Publication checks
are recorded in `publication-checks.json` when completed. This is not a cold
source replay or an independent review.

The original model-category infrastructure comes from the pinned Part I
dependency, which in turn pins Mathlib. This new layout preserves the module
names and source bytes. Its public alias is `DaggerModelsPartIICompanion.mainC`.

## Pending external verification

No new hosted Linux CI, independent Mathlib-only Challenge, real Comparator
replay with negative controls, or independent human manuscript review is
claimed. The manual workflow has not been triggered for this release.
A byte/hash evidence checker is not a theorem prover or a Comparator substitute.
