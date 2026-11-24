import DaggerModelsPartII.JTOrderedLabelPaddingDiagram
import DaggerModelsPartII.JTSemiSimplexElementsWeak
import DaggerModelsPartII.GrothendieckNerveMapWeak

/-! Retain all extension simplices while restricting their time operators to injections. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingSemiIndex

open JTOrderedLabelPaddingDiagram (along)
open GrothendieckTotalElements (totalDiagram fromTotal toTotal equivalence)
open SemiSimplexCategory (toSimplexCategory)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

section SimplicialDiagram

variable {B : Type} [SmallCategory B] (X : B ⥤ SSet.{0})

private abbrev reduced : B ⥤ SemiSimplexCategoryᵒᵖ ⥤ Type :=
  X ⋙ (Functor.whiskeringLeft _ _ (Type 0)).obj toSimplexCategory.op

/-- All simplices of every diagram value, with only injective time operators. -/
abbrev Index := (totalDiagram (reduced X)).Elementsᵒᵖ

private abbrev comparison :
    GrothendieckTotalElements.elementDiagram (reduced X) ⟶
      GrothendieckTotalElements.elementDiagram X :=
  Functor.whiskerLeft X JTSemiSimplexElementsWeak.elementForgetUnopNat

/-- Regard the same simplex and its injective time arrows in the full category. -/
def toFull : Index X ⥤ (totalDiagram X).Elementsᵒᵖ :=
  (fromTotal (reduced X) ⋙ Grothendieck.map (comparison X) ⋙ toTotal X).op

/-- Restricting to injective time operators keeps the whole weak nerve type. -/
theorem toFull_weak : WeakEquivalence (nerveMap (toFull X)) := by
  let E := fromTotal (reduced X)
  let F := toTotal X
  let β := comparison X
  letI : WeakEquivalence (nerveMap E) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence
      (equivalence (reduced X)).inverse
  letI : WeakEquivalence (nerveMap F) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence
      (equivalence X).functor
  have hβ (p : B) : WeakEquivalence (nerveMap (β.app p).toFunctor) :=
    (TotalElementsWeakComparison.nerveMap_op_iff
      (JTSemiSimplexElementsWeak.elementForgetUnop (X.obj p))).mp
      (JTSemiSimplexElementsWeak.elementForget_weakEquivalence (X.obj p))
  letI : WeakEquivalence (nerveMap (Grothendieck.map β)) :=
    GrothendieckNerveMapWeak.map_weak β hβ
  have h : WeakEquivalence (nerveMap E ≫ nerveMap (Grothendieck.map β) ≫ nerveMap F) :=
    inferInstance
  exact (TotalElementsWeakComparison.nerveMap_op_iff (E ⋙ Grothendieck.map β ⋙ F)).mpr h

end SimplicialDiagram

/-- The injective-time index of padded extensions gives a weak cover of the original base. -/
theorem base_weak {A : Type} [SmallCategory A] (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (L : A ⥤ OrderedLabelElements.Index W b)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toFull (along W b L) ⋙ JTOrderedLabelPaddingDiagram.base W b L)) := by
  letI := toFull_weak (along W b L)
  letI := JTOrderedLabelPaddingDiagram.base_weak W b L hW
  change WeakEquivalence
    (nerveMap (toFull (along W b L)) ≫ nerveMap (JTOrderedLabelPaddingDiagram.base W b L))
  infer_instance

end

end DaggerModels.PartII.JTOrderedLabelPaddingSemiIndex
