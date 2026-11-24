# Part II Theorem C publication scope

The author authorized a separate public repository on November 25, 2026.
This release candidate contains an AI-assisted local Lean proof of the original
universe-zero four-link Theorem C, its supporting sources, saved local evidence,
and an English PDF catalogue using Part II notation.

The existing Part I repository and its release records are separate. This
repository requires Part I at commit
`9ee62295a79ef61269259e27216afc0292458931`; it does not republish that dependency's
source tree or carry its CI certificates forward as evidence for Part II.

The original proof used 359 named stages and 3,081 project-source modules across
the original workspace. Its 156 direct project import roots passed a Lake
content-rehash/no-build freshness gate. All 359 stages have successful local
kernel receipts, source/import hashes and 1,182 printed standard axiom reports.
The final theorem and four literal component targets were checked and freshly
rechecked from saved sources. A public entry-point alias and the separate
repository configuration are checked as recorded in `verification/`.

Source bytes are preserved. Public stage receipts are normalized exports:
private filesystem paths and original command strings were omitted, while
source hashes, unchanged log bytes, artifact hashes, actual exits, durations,
import hashes and hashes of the original private receipts are retained.
They are not described as byte-identical copies of the original receipt JSON.

A cold full build of this new repository, hosted Linux verification, a new
Comparator run with negative controls, an independent Mathlib-only Challenge,
and independent human correspondence review have not been completed.
The optional workflow is manual, and no long CI is started for publication.

The catalogue groups substantial theorem/proposition-level results. It is not
a statement that every source file is an independent major theorem or a new
mathematical contribution.
