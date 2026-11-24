import OrdinarySegalHorizontalRestrictions
import RelativeRightOuterHornFilling

/-!
# Relative outer-horn lifting for noncomplete ordinary Segal restrictions

Apply the actual inner-fibration outer-horn theorem to the vertical limit
restriction induced by a monomorphism. Its source and target quasicategories
and relative inner-horn property follow from the spine-only Segal hypothesis.
The supplied simplex in the target restriction remains the exact image of
the constructed lift. No ordinary completeness hypothesis is imposed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalRightOuterHornInclusions
open DaggerOriginalRelativeRightOuterHornFilling

namespace DaggerModels.PartII.OrdinarySegalRelativeOuterHorn

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- A right outer horn in a vertical restriction lifts over the specified
base simplex whenever its same original last edge is invertible. -/
theorem restriction_right_outer_horn_lift (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{0}) ⟶
      diagramRestriction L W.flip)
    (β : (Δ[k + 2] : SSet.{0}) ⟶ diagramRestriction K W.flip)
    (w : φ ≫ diagramRestrictionPre v W.flip =
      Λ[k + 2, Fin.last (k + 2)].ι ≫ β)
    (he : edgeIsInvertible (diagramRestriction L W.flip)
      (SSet.yonedaEquiv (rightOuterLastEdgeInclusion k ≫ φ))) :
    ∃ σ : (Δ[k + 2] : SSet.{0}) ⟶ diagramRestriction L W.flip,
      φ = Λ[k + 2, Fin.last (k + 2)].ι ≫ σ ∧
        σ ≫ diagramRestrictionPre v W.flip = β := by
  have hC : innerHornFillers (diagramRestriction L W.flip) :=
    (innerHornFillers_iff_native_quasicategory _).mpr
      (OrdinarySegalHorizontalRestrictions.restriction_quasicategory W hSegal L)
  have hD : innerHornFillers (diagramRestriction K W.flip) :=
    (innerHornFillers_iff_native_quasicategory _).mpr
      (OrdinarySegalHorizontalRestrictions.restriction_quasicategory W hSegal K)
  exact right_outer_horn_filler_over (diagramRestrictionPre v W.flip)
    (OrdinarySegalHorizontalRestrictions.restriction_innerFibration W hSegal v)
    hC hD k φ β w he

#print axioms restriction_right_outer_horn_lift

end

end DaggerModels.PartII.OrdinarySegalRelativeOuterHorn
