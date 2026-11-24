# Part II companion publication scope

The author authorized this separate public repository on November 25, 2026.
Release candidate v0.1.0-rc2 expands the original C-focused companion to an
English catalogue across Part II, including the original Theorems A, B and C.
The earlier v0.1.0-rc1 tag and release are retained unchanged.

## Catalogue and current checks

There are 49 grouped entries: three main theorems and 46 substantial supporting
propositions or construction theorems, with 166 distinct Lean declaration roots.
The groups are not independent theorem counts or claims of new mathematical
novelty. Contextual manuscript labels do not certify every clause of that label.
The English prose and selection are AI-generated and disclosed on the first page.

The current main A/B/C aliases passed a fresh local compile. The exact 166 roots
passed a separate local transitive axiom audit using only propext,
Classical.choice and Quot.sound. Their 68 native owner modules passed a current
original-source Lake content-rehash/no-build gate. The A/B proof graphs also
passed a separate freshness gate. All 1392 exported native Part II source bytes
match the original workspace. The new aliases preserve the original statements;
no theorem hypotheses or universes were changed for this publication.

Theorem A retains its universe parameter. The full Theorem B includes the literal
simplicial structure and is assembled at universe zero. Theorem C retains its
original universe-zero four-link statement, without added source completeness.
Saved current results and AI correspondence review are in
`verification/catalogue-20261125/`. Independent human review is pending.

## Earlier evidence

Historical A/B evidence records the November 8 aggregate and overlapping owner
audits. The current aggregate and two frame sources have since changed, so that
milestone is not claimed as a fresh audit of the current entire tree.

The original final C proof used 359 named stages, 1182 printed standard axiom
reports and a 156-root source freshness gate. Its final proof and four literal
component targets were also recompiled from saved sources. Those C-specific
counts remain separate from the expanded catalogue's 166 advertised roots.

Public JSON receipts normalize private machine paths and original command strings.
Source and axiom-log bytes, actual exits, durations, artifact/import hashes and
hashes of private originals are retained as described by each record.

## Dependencies and limits

Part I remains a separate dependency fixed at commit
`9ee62295a79ef61269259e27216afc0292458931`. Its source tree is not republished
here, and its CI certificates are not carried forward as Part II certificates.

Current checks use verified existing import caches. A cold full build of this
repository, new hosted Linux verification, real Comparator replay with negative
controls, independent Mathlib-only Challenges and independent human
correspondence review are not claimed. The workflow remains manual and no long
CI is triggered. Log-validator negative controls are not Comparator tests.

The source archive and PDF are bound to the release commit by per-file hashes,
`release-record.json` and `SHA256SUMS`. The archive is read back against all
committed files and is reproducible through `scripts/build_release_bundle.py`.
