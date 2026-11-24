# Correspondence with Part II Theorem C

This is an AI-assisted correspondence record, not independent human review.

The manuscript names the dagger Joyal--Tierney equivalence in `jt.thm.main`
and the resulting four-link zigzag in `jt.cor.goal`, also stated as Theorem C
in the introduction. The exact Lean specification is
[`TheoremCStatement.statement`](../lean/DaggerModelsPartII/TheoremCStatement.lean).
The source specification and manuscript were unchanged when the proof passed.

| Link | Left adjoint | Right adjoint | Source of the left adjoint | Target of the left adjoint |
| --- | --- | --- | --- | --- |
| Part I rigidification | dagger rigidification | dagger coherent nerve | dagger Joyal | dagger Bergner |
| Constant--vertex | delta | vertex evaluation i_0^* | dagger Joyal | injective localized reversal spaces |
| Identity | identity | identity | projective localized reversal spaces | injective localized reversal spaces |
| Index change | actual left extension u_! | actual restriction u^* | projective localized reversal spaces | projective localized actual-index spaces |

The manuscript's left-to-right zigzag displays the right adjoints above the
rightward arrows in the first and third links. The table instead uniformly
lists each left adjoint and its own source and target.

The fixed theorem is at value universe zero. It does not claim an arbitrary-
universe assembly. Its proof first discharges the exact original
`OriginalRawOrderedUnitWeak` premise by showing that the original
`rawChosenFiberMapAtP` is weak at the specified original projective-image
vertices. The source has the original reversal-local hypothesis; ordinary
completeness is not added.

The ordinary argument uses the checked corrected vertical precompletion,
an injectively fibrant replacement, complete-Segal recognition, Mathlib model
factorization and lifting, and the existing ordinary Joyal--Tierney comparison.
Composition of chosen ordered-fiber maps is compared after Kan localization;
no unproved point-set functoriality is substituted.

The final four conclusions are also checked separately in
[`TheoremCOriginalFourLinksAudit`](../lean/TheoremCStages/TheoremCOriginalFourLinksAudit.lean).
This literal target audit is not a Mathlib-only Challenge or a Comparator run.
An AI agent reviewed the original statement, manuscript labels, final proof
and literal targets and found no concrete mismatch. That is not human review.

The final proof does not assert a general total-derived-functor API, nor does
it close every intermediate claim from the older finite-support contraction
route. Those are not additional premises of the now-proved original statement.
