import DaggerModelsPartII.JTOrderedLabelPaddingPrismDiagram
import DaggerModelsPartII.SemiSimplexBoundaryComparison

/-! Compare the exact total category of ordered realizations to the original base. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismCover

open JTOrderedLabelPaddingPrismDiagram (mixed forget)
open JTOrderedLabelPaddingDiagram (along FullIndex)
open GrothendieckTotalElements (totalDiagram fromTotal toTotal elementDiagram equivalence)
open SemiSimplexBoundaryLifting (HasBoundaryLifting toFullElements toFullElements_weak)

noncomputable section

private abbrev toSemiPresheaf : SSet.{0} ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft _ _ _).obj SemiSimplexCategory.toSimplexCategory.op

section Diagrams

variable {B : Type} [SmallCategory B]
variable (M : B × SemiSimplexCategoryᵒᵖ ⥤ Type) (X : B ⥤ SSet.{0})
variable (α : Functor.curryObj M ⟶ X ⋙ toSemiPresheaf)

private def uncurryEquiv :
    M.Elements ≌ (totalDiagram (Functor.curryObj M)).Elements :=
  Cat.equivOfIso (Functor.elementsFunctor.mapIso (Functor.currying.counitIso.app M).symm)

private def comparison : elementDiagram (Functor.curryObj M) ⟶ elementDiagram X :=
  Functor.whiskerRight α Functor.elementsFunctor ≫
    Functor.whiskerLeft X JTSemiSimplexElementsWeak.elementForgetUnopNat

private abbrev toFullUnop : M.Elements ⥤ (totalDiagram X).Elements :=
  (uncurryEquiv M).functor ⋙ fromTotal (Functor.curryObj M) ⋙
    Grothendieck.map (comparison M X α) ⋙ toTotal X

private abbrev toFullDiagram : M.Elementsᵒᵖ ⥤ (totalDiagram X).Elementsᵒᵖ :=
  (toFullUnop M X α).op

private theorem toFullUnop_base :
    toFullUnop M X α ⋙ CategoryOfElements.π (totalDiagram X) ⋙
        CategoryTheory.Prod.fst B SimplexCategoryᵒᵖ =
      CategoryOfElements.π M ⋙ CategoryTheory.Prod.fst B SemiSimplexCategoryᵒᵖ := rfl

private theorem toFullDiagram_weak
    (h : ∀ p : B, HasBoundaryLifting (α.app p)) :
    WeakEquivalence (nerveMap (toFullDiagram M X α)) := by
  let β := comparison M X α
  have hβ (p : B) : WeakEquivalence (nerveMap (β.app p).toFunctor) := by
    apply (TotalElementsWeakComparison.nerveMap_op_iff ((β.app p).toFunctor)).mp
    change WeakEquivalence (nerveMap (toFullElements (α.app p)))
    exact (weakEquivalence_iff_GW _).mpr (toFullElements_weak (h p))
  let F := (uncurryEquiv M).functor
  let G := fromTotal (Functor.curryObj M)
  let H := toTotal X
  letI : WeakEquivalence (nerveMap F) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence F
  letI : WeakEquivalence (nerveMap G) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence
      (equivalence (Functor.curryObj M)).inverse
  letI : WeakEquivalence (nerveMap H) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence
      (equivalence X).functor
  letI : WeakEquivalence (nerveMap (Grothendieck.map β)) :=
    GrothendieckNerveMapWeak.map_weak β hβ
  have hcomp : WeakEquivalence
      (nerveMap F ≫ nerveMap G ≫ nerveMap (Grothendieck.map β) ≫ nerveMap H) := inferInstance
  exact (TotalElementsWeakComparison.nerveMap_op_iff (F ⋙ G ⋙ Grothendieck.map β ⋙ H)).mpr hcomp

end Diagrams

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable {A : Type} [SmallCategory A]
variable (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

/-- The exact index retaining the realization, extension simplex, and two original operators. -/
abbrev Index := (mixed W b L).Elementsᵒᵖ

/-- Forget just the realization and admit all operators in the extension simplex direction. -/
abbrev toFull : Index W b L ⥤ FullIndex W b L :=
  toFullDiagram (mixed W b L) (along W b L) (forget W b L)

/-- Boundary lifting at every old label gives weakness of the full mixed comparison. -/
theorem toFull_weak_of
    (h : ∀ p : Aᵒᵖ, HasBoundaryLifting ((forget W b L).app p)) :
    WeakEquivalence (nerveMap (toFull W b L)) :=
  toFullDiagram_weak (mixed W b L) (along W b L) (forget W b L) h

/-- The projection to the unchanged label and time operators before realization. -/
abbrev positiveBase : Index W b L ⥤ A × SemiSimplexCategory :=
  (CategoryOfElements.π (mixed W b L) ⋙
    (prodOpEquiv (C := A) (D := SemiSimplexCategory)).inverse).leftOp

/-- The weak comparison projects by precisely the original base arrow. -/
theorem toFull_base :
    toFull W b L ⋙ JTOrderedLabelPaddingDiagram.base W b L =
      positiveBase W b L ⋙ CategoryTheory.Prod.fst A SemiSimplexCategory :=
  congrArg (fun F ↦ F.leftOp) (toFullUnop_base (mixed W b L) (along W b L) (forget W b L))

/-- A choice of relative ordered realizations gives an actual weak cover of the original base. -/
theorem base_weak_of
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (h : ∀ p : Aᵒᵖ, HasBoundaryLifting ((forget W b L).app p)) :
    WeakEquivalence (nerveMap (positiveBase W b L ⋙
      CategoryTheory.Prod.fst A SemiSimplexCategory)) := by
  rw [← toFull_base]
  letI := toFull_weak_of W b L h
  letI := JTOrderedLabelPaddingDiagram.base_weak W b L hW
  change WeakEquivalence
    (nerveMap (toFull W b L) ≫ nerveMap (JTOrderedLabelPaddingDiagram.base W b L))
  infer_instance

end

end DaggerModels.PartII.JTOrderedLabelPaddingPrismCover
