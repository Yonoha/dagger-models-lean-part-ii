import DaggerModelsPartII.JTOrderedLabelPaddingPrismFiber
import DaggerModelsPartII.JTOrderedLabelPaddingPrismBoundary
import DaggerModelsPartII.JTOrderedLabelPaddingPrismCover
import DaggerModelsPartII.JTOrderedLabelPaddingPrismSliceArrow

/-! The exact cover by chosen ordered prism realizations is weak over the original base. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismWeakCover

open JTOrderedLabelPaddingPrismDiagram (choices forget)
open JTOrderedLabelPaddingPrismCover (toFull positiveBase toFull_weak_of base_weak_of)
open SemiSimplexBoundaryLifting (HasBoundaryLifting)
open SemiSimplexCategory (toSimplexCategory)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable {A : Type} [SmallCategory A]
variable (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

private abbrev Y (p : Aᵒᵖ) :=
  (OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).obj
    (op (OrderedLabelElements.necklace W b (L.obj p.unop)))
private abbrev k (p : Aᵒᵖ) := OrderedLabelElements.degree W b (L.obj p.unop)
private abbrev z (p : Aᵒᵖ) := OrderedLabelElements.label W b (L.obj p.unop)

private abbrev fixed (p : Aᵒᵖ) :=
  JTOrderedLabelPaddingPrismBoundary.choices (Y W b L p) (k W b L p) (z W b L p)

private def fixedEquiv (p : Aᵒᵖ) (d : SemiSimplexCategoryᵒᵖ) :
    ((choices W b L).obj p).obj d ≃ (fixed W b L p).obj d :=
  (JTOrderedLabelPaddingPrismBoundary.pairEquiv
    (Y W b L p) (k W b L p) (z W b L p) (toSimplexCategory.obj d.unop)).symm

set_option maxHeartbeats 800000 in
private theorem fixedEquiv_natural (p : Aᵒᵖ) {m n : SemiSimplexCategoryᵒᵖ}
    (j : m ⟶ n) (s : ((choices W b L).obj p).obj m) :
    fixedEquiv W b L p n (((choices W b L).obj p).map j s) =
      (fixed W b L p).map j (fixedEquiv W b L p m s) := by
  apply JTCommonCoefficientLiftChoices.Extension.ext
  exact JTOrderedLabelPaddingPrismFiber.map_val W b L p j.unop s

/-- The mixed fiber over an exact old label is the fixed relative enlargement. -/
def fixedIso (p : Aᵒᵖ) : (choices W b L).obj p ≅ fixed W b L p :=
  NatIso.ofComponents (fun d ↦ (fixedEquiv W b L p d).toIso) (by
    intro m n j
    funext s
    exact fixedEquiv_natural W b L p j s)

private theorem forget_fixed (p : Aᵒᵖ) : (forget W b L).app p =
    (fixedIso W b L p).hom ≫
      JTOrderedLabelPaddingPrismBoundary.forget (Y W b L p) (k W b L p) (z W b L p) := by
  ext d s
  have h := (JTOrderedLabelPaddingPrismBoundary.pairEquiv
    (Y W b L p) (k W b L p) (z W b L p) (toSimplexCategory.obj d.unop)).apply_symm_apply s
  exact (congrArg Sigma.fst h).symm

/-- All actual label fibers admit relative lifting of compatible enlarged time faces. -/
theorem boundary_lifting
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : Aᵒᵖ) : HasBoundaryLifting ((forget W b L).app p) := by
  letI : IsFibrant (Y W b L p) :=
    JTOrderedLabelPaddingDiagram.label_isFibrant W b (L.obj p.unop) hW
  rw [forget_fixed]
  exact (JTOrderedLabelPaddingPrismBoundary.hasBoundaryLifting _ _ _).precompIso _

/-- Forgetting the exact realization is a nerve weak equivalence. -/
theorem toFull_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toFull W b L)) :=
  toFull_weak_of W b L (boundary_lifting W b L hW)

/-- The exact realization index, with its original base arrows, is a weak cover. -/
theorem base_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (positiveBase W b L ⋙
      CategoryTheory.Prod.fst A SemiSimplexCategory)) :=
  base_weak_of W b L hW (boundary_lifting W b L hW)

/-- The base used to pull back the original graph family is the exact weak projection. -/
theorem originalBase_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (JTOrderedLabelPaddingPrismSliceArrow.originalBase W b L)) :=
  base_weak W b L hW

end

end DaggerModels.PartII.JTOrderedLabelPaddingPrismWeakCover
