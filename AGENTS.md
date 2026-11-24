# Lean companion workflow

Preserve the manuscript's definitions, hypotheses, universes, adjoints and
directions. Explain mathematical changes before making them. A successful Lean
build does not establish manuscript correspondence.

Use the lean4 skill and search the pinned Mathlib and Part I dependencies before
new proofs. Prefer compatible existing results. Follow the author's preference
for bounded gpt-6-sol/high implementation or review agents when useful.

The stage sources retain their original bare module names. Their source root is
`lean/TheoremCStages`; native Part II modules use `lean/DaggerModelsPartII`.
Do not rewrite imports merely to move folders. Keep the Part I dependency pin
and the original Theorem C statement fixed unless a change is explained.

Keep local kernel evidence, source freshness, full builds, hosted CI, Comparator,
AI review and independent human review distinct. Trusted Challenges must import
only pinned Mathlib, with all needed definitions visible, and should be short.
The literal four-link audit is not an independent Challenge. Do not silently
replace the trusted problem with candidate definitions.

The author requested no long CI for this publication. The workflow is manual.
Do not infer a hosted pass from saved local receipts. Keep formalization.yaml
and the English catalogue honest about verification scope and AI assistance.
