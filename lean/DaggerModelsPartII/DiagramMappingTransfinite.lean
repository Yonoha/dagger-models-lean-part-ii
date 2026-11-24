import DaggerModelsPartII.DiagramMappingLimits
import DaggerModelsPartII.InverseTowerLifting
import TopCatModelCategory.ModelCategorySSet

/-!
# Strict mapping spaces and transfinite compositions

For a continuous well ordered diagram, a strict mapping space sends the colimit
to the inverse limit of its mapping spaces. If every successor map in that
inverse tower is a trivial Kan fibration, so is the map to its bottom stage.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u v

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]
  {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

/-- Strict mapping-space precomposition along the bottom-to-colimit map is a
trivial Kan fibration when this holds at every successor stage. -/
theorem diagramMappingPrecomp_colimit_trivialFibration
    (X : J ⥤ (C ⥤ SSet.{u})) [X.IsWellOrderContinuous]
    {cX : Cocone X} (hX : IsColimit cX) (W : C ⥤ SSet.{u})
    (h : ∀ (j : J), ¬ IsMax j →
      trivialFibrations SSet.{u}
        (diagramMappingPrecomp (X.map (homOfLE (Order.le_succ j))) W)) :
    trivialFibrations SSet.{u} (diagramMappingPrecomp (cX.ι.app ⊥) W) := by
  let F := diagramMappingSource W
  let G := X.op ⋙ F
  letI : HasColimitsOfSize.{0, u} SSet.{u} := hasColimitsOfSizeShrink.{0, u} _
  letI : HasColimitsOfSize.{0, u} (C ⥤ SSet.{u}) := hasColimitsOfSizeShrink.{0, u} _
  letI : (X.op).rightOp.IsWellOrderContinuous := by
    change (X ⋙ opOp (C ⥤ SSet.{u})).IsWellOrderContinuous
    letI : PreservesWellOrderContinuousOfShape J (opOp (C ⥤ SSet.{u})) :=
      ⟨fun _ _ ↦ inferInstance⟩
    infer_instance
  letI : G.rightOp.IsWellOrderContinuous :=
    inverseTower_continuous_map X.op F
      (fun j _ ↦ diagramMappingSource_preservesLimitsOfShape (Set.Iio j)ᵒᵖ W)
  letI : PreservesLimitsOfShape Jᵒᵖ F :=
    diagramMappingSource_preservesLimitsOfShape Jᵒᵖ W
  have hm : SSet.modelCategoryQuillen.I.rlp (F.map (cX.ι.app ⊥).op) := by
    change SSet.modelCategoryQuillen.I.rlp
      ((F.mapCone cX.op).π.app (op ⊥))
    apply rlp_limitProjection_of_inverseTower _ G (isLimitOfPreserves F hX.op)
    intro j hj
    rw [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
    exact h j hj
  rw [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations] at hm
  exact hm

end

end DaggerModels.PartII
