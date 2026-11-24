import OrdinarySegalRelativeOuterHorn
import RelativeSelectedLeftOuterHornFilling

/-!
# Selected relative left outer horns in the original Segal restrictions

The literal first edge controls the lifting problem in the same vertical
restriction of an ordinary Segal space. Completeness is not used. This is
the orientation of the outer-horn attachments in the alternating filtration
of the original walking isomorphism.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerModels.PartII.RelativeLeftOuterHornGeometry
open DaggerModels.PartII.RelativeSelectedLeftOuterHornFilling

namespace DaggerModels.PartII.OrdinarySegalRelativeLeftOuterHorn

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The first edge of the supplied left horn determines one exact
relative filler over the originally prescribed base simplex. -/
theorem restriction_left_outer_horn_lift (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] (k : ℕ)
    (φ : (Λ[k + 2, (0 : Fin (k + 3))] : SSet.{0}) ⟶
      diagramRestriction L W.flip)
    (β : (Δ[k + 2] : SSet.{0}) ⟶ diagramRestriction K W.flip)
    (w : φ ≫ diagramRestrictionPre v W.flip =
      Λ[k + 2, (0 : Fin (k + 3))].ι ≫ β)
    (he : edgeIsInvertible (diagramRestriction L W.flip)
      (SSet.yonedaEquiv (firstEdgeInclusion k ≫ φ))) :
    ∃ σ : (Δ[k + 2] : SSet.{0}) ⟶ diagramRestriction L W.flip,
      φ = Λ[k + 2, (0 : Fin (k + 3))].ι ≫ σ ∧
        σ ≫ diagramRestrictionPre v W.flip = β := by
  have hC : innerHornFillers (diagramRestriction L W.flip) :=
    (innerHornFillers_iff_native_quasicategory _).mpr
      (OrdinarySegalHorizontalRestrictions.restriction_quasicategory W hSegal L)
  have hD : innerHornFillers (diagramRestriction K W.flip) :=
    (innerHornFillers_iff_native_quasicategory _).mpr
      (OrdinarySegalHorizontalRestrictions.restriction_quasicategory W hSegal K)
  exact selected_left_outer_horn_filler_over (diagramRestrictionPre v W.flip)
    (OrdinarySegalHorizontalRestrictions.restriction_innerFibration W hSegal v)
    hC hD k φ β w he

#print axioms restriction_left_outer_horn_lift

end

end DaggerModels.PartII.OrdinarySegalRelativeLeftOuterHorn
