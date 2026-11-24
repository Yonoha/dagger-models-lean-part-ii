import OrdinaryCoherentRelativeReflection
import OrdinaryCoherentReplacementPreimage
import OrdinaryCoherentWeakInvariance
import OrdinarySegalCotensorFibrant

/-!
# The exact coherent preimage at original diagonal vertices

The corrected unit is the original E[0] constant section at vertical degree
zero, hence an actual isomorphism there. Coherent reflection of the same unit
followed by the replacement therefore identifies the actual diagonal range
with the preimage of the replacement coherent subcomplex on vertices.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentReplacementVertexPreimage

open OrdinaryCSSLocalization (Space)
open OrdinaryCoherentReplacementComparison (diagonalInclusion)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalVerticalPrecompletion (precompletion unit)

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

/-- The literal diagonal range tests membership in the original coherent row. -/
theorem range_mem_iff (W : Space) (q : SimplexCategoryᵒᵖ)
    (x : ((precompletion W).obj (op ⦋1⦌)).obj q) :
    x ∈ (SSet.Subcomplex.range (diagonalInclusion W)).obj q ↔
      x ∈ (coherentArrowSubcomplex
        (OrdinarySegalHorizontalCotensor.cotensor
          (GroupoidSimplex.parameter.obj q.unop) W)).obj q := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- At the same original vertex, the unit detects the exact diagonal coherent range. -/
theorem unit_zero_range_iff (W : Space) [IsFibrant W]
    (u : (W.obj (op ⦋1⦌)).obj zero) :
    ((unit W).app (op ⦋1⦌)).app zero u ∈
        (SSet.Subcomplex.range (diagonalInclusion W)).obj zero ↔
      u ∈ (coherentArrowSubcomplex W).obj zero := by
  let K := GroupoidSimplex.parameter.obj ⦋0⦌
  haveI : IsFibrant (OrdinarySegalHorizontalCotensor.cotensor K W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant K W inferInstance
  haveI : IsIso (constantSection K W) :=
    OrdinarySegalVerticalPrecompletion.constantSection_zero_isIso W
  rw [range_mem_iff, OrdinarySegalVerticalPrecompletion.unit_app_app_apply]
  exact (OrdinaryCoherentWeakInvariance.coherent_membership_iff
    (constantSection K W) zero u).symm

/-- The same specified replacement has exactly the original coherent preimage
on diagonal vertices; no replacement completeness is used. -/
theorem replacement_vertex_preimage (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j))
    (x : ((precompletion W).obj (op ⦋1⦌)).obj zero) :
    x ∈ (SSet.Subcomplex.range (diagonalInclusion W)).obj zero ↔
      (i.app (op ⦋1⦌)).app zero x ∈ (coherentArrowSubcomplex R).obj zero := by
  haveI : IsIso (NatTrans.flipApp (unit W) zero) :=
    OrdinarySegalVerticalPrecompletion.unit_verticalZero_isIso W
  haveI : IsIso (((unit W).app (op ⦋1⦌)).app zero) := by
    change IsIso ((NatTrans.flipApp (unit W) zero).app (op ⦋1⦌))
    infer_instance
  obtain ⟨u, rfl⟩ := ((isIso_iff_bijective
    (((unit W).app (op ⦋1⦌)).app zero)).mp inferInstance).surjective x
  rw [unit_zero_range_iff]
  exact OrdinaryCoherentRelativeReflection.replacement_reflects W hSegal R i hi zero u

#print axioms range_mem_iff
#print axioms unit_zero_range_iff
#print axioms replacement_vertex_preimage

end

end DaggerModels.PartII.OrdinaryCoherentReplacementVertexPreimage
