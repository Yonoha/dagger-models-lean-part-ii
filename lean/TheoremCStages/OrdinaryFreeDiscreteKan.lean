import OrdinaryCSSLocalization
import DaggerModelsPartII.IndexKanExtensions
import DaggerModelsPartII.ReversalDiscreteFreeColimits

/-!
# Free reversal extension of an ordinary discrete simplicial space

The horizontal left Kan extension of an ordinary, vertically discrete
simplicial space is the existing discrete free dagger construction. The
isomorphism is natural in the entire ordinary simplicial set, so it also
identifies its spine and boundary maps without changing their sources.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Simplicial
open DaggerModels

namespace DaggerModels.PartII.OrdinaryFreeDiscreteKan

noncomputable section

private abbrev Base := SimplexCategoryᵒᵖ ⥤ Type 0
private abbrev Extended := ReverseSimplexᵒᵖ ⥤ Type 0
private abbrev ordinaryDiscrete := OrdinaryCSSLocalization.discrete
private abbrev freeDiscrete := ReversalDiscreteFreeColimits.discreteFree.{0}

/-- The literal ordinary discrete embedding followed by horizontal left
extension agrees with the original Part I free dagger, discretized in the
vertical simplicial direction. -/
def discreteExtensionIso :
    ordinaryDiscrete ⋙ extendIndexLeft.{0, 0} ReverseSimplex.inclusion ≅
      freeDiscrete := by
  let F := ReverseSimplex.inclusion.op
  let C : Type 0 ⥤ SSet.{0} := SimplicialObject.const (Type 0)
  letI : ∀ V : Base, F.HasLeftKanExtension V := by
    intro V
    letI : F.HasPointwiseLeftKanExtension V := fun _ ↦ inferInstance
    infer_instance
  letI : ∀ V : OrdinaryCSSLocalization.Space,
      F.HasLeftKanExtension V := by
    intro V
    letI : HasColimitsOfSize.{0, 0} SSet.{0} :=
      hasColimitsOfSizeShrink.{0, 0, 0, 0} _
    letI : F.HasPointwiseLeftKanExtension V := fun _ ↦ inferInstance
    infer_instance
  letI : PreservesColimitsOfSize.{0, 0} C := by
    change PreservesColimitsOfSize.{0, 0} (SimplicialObject.const (Type 0))
    exact CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)
  letI : C.PreservesLeftKanExtensions F := by
    intro V
    letI : F.HasPointwiseLeftKanExtension V := fun _ ↦ inferInstance
    letI : C.PreservesPointwiseLeftKanExtension V F := fun _ ↦ inferInstance
    infer_instance
  let K : Base ⥤ Extended := F.lan
  let J : OrdinaryCSSLocalization.Space ⥤
      SegalLocalizers.ReverseDaggerSpace.{0} := F.lan
  let E : Base ⥤ OrdinaryCSSLocalization.Space :=
    (whiskeringRight _ _ _).obj C
  let D : Extended ⥤ SegalLocalizers.ReverseDaggerSpace.{0} :=
    (whiskeringRight _ _ _).obj C
  let P := ReversePresheaf.toDaggerSSet.{0}
  let Q := DaggerSSet.toPresheaf.{0}
  change E ⋙ J ≅ (K ⋙ P) ⋙ (Q ⋙ D)
  exact (C.lanCompIsoOfPreserves F).symm ≪≫
    isoWhiskerRight (Functor.rightUnitor K).symm D ≪≫
    isoWhiskerRight (isoWhiskerLeft K ReversePresheaf.counitIso.symm) D ≪≫
    isoWhiskerRight (Functor.associator K P Q).symm D ≪≫
    Functor.associator (K ⋙ P) Q D

#print axioms discreteExtensionIso

end

end DaggerModels.PartII.OrdinaryFreeDiscreteKan
