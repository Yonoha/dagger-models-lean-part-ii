import DaggerModelsPartII.TimePrismChainDiagram
import DaggerModelsPartII.JTOrderedLabelPaddingPrismSliceArrow
import DaggerModelsPartII.JTOrderedLabelPaddingPrismCover
import DaggerModelsPartII.JTOrderedLabelPaddingChainComparison

/-! Compare the actual old and realized labels along all ordered prism chains. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismChains

open JTOrderedLabelPaddingPrismSliceArrow (originalBase)
open JTOrderedLabelPaddingPrismLabels (labelIndex)
open JTOrderedLabelPaddingChainComparison (chainMap chainMap_map chainMap_precomp chain_interior_fixed)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable {A : Type} [SmallCategory A]
variable (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

private abbrev E := (JTOrderedLabelPaddingPrismDiagram.mixed W b L).Elementsᵒᵖ
private abbrev P := OrderedLabelElements.projection W b
private abbrev degree (M : E W b L ⥤ OrderedLabelElements.Index W b) :=
  M ⋙ P W b ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory

/-- The original coefficient degree on the realization index. -/
abbrev coefficient := degree W b L (originalBase W b L ⋙ L)

/-- The actual injective time operator of the original realization index. -/
abbrev time :=
  JTOrderedLabelPaddingPrismCover.positiveBase W b L ⋙
    CategoryTheory.Prod.snd A SemiSimplexCategory ⋙ SemiSimplexCategory.toSimplexCategory

/-- The full index of chosen realizations with chains covering their old coefficients. -/
abbrev Index := TimePrismChainDiagram.Index (coefficient W b L) (time W b L)

/-- The forgetful functor still retains the native, coefficient, and time operators. -/
abbrev base : Index W b L ⥤ E W b L :=
  TimePrismChainDiagram.base (coefficient W b L) (time W b L)

/-- The original label in a chain chart. -/
abbrev oldLabels : Index W b L ⥤ OrderedLabelElements.Index W b :=
  base W b L ⋙ originalBase W b L ⋙ L

/-- The realized label in the same chart, on the same actual native code. -/
abbrev realizedLabels : Index W b L ⥤ OrderedLabelElements.Index W b :=
  base W b L ⋙ labelIndex W b L

abbrev ordinals := TimePrismChainDiagram.ordinals (coefficient W b L) (time W b L)

/-- The coefficient projection of the ordered chain is surjective. -/
abbrev toOriginal : ordinals W b L ⟶ base W b L ⋙ coefficient W b L :=
  TimePrismChainDiagram.coeffProjection (coefficient W b L) (time W b L)

private abbrev toTime :=
  TimePrismChainDiagram.timeProjection (coefficient W b L) (time W b L)

/-- Include each complete ordered chain into its actual realized prism. -/
def toRealized : ordinals W b L ⟶ base W b L ⋙ degree W b L (labelIndex W b L) where
  app p := chainMap ((toOriginal W b L).app p) ((toTime W b L).app p)
  naturality {p q} f := by
    let g := (coefficient W b L).map ((base W b L).map f)
    let j := (time W b L).map ((base W b L).map f)
    have hj : Function.Injective j.toOrderHom :=
      (SemiSimplexCategory.homEquiv ((base W b L).map f).unop.val.2.unop).injective
    change (ordinals W b L).map f ≫ chainMap ((toOriginal W b L).app q) ((toTime W b L).app q) =
      chainMap ((toOriginal W b L).app p) ((toTime W b L).app p) ≫
        JTCommonCoefficientParameter.map (JTPaddedTimeOperators.map g)
          (JTOrderedLabelPaddingPrism.map_blocks g) j hj
    rw [chainMap_precomp, chainMap_map]
    exact congrArg₂ chainMap ((toOriginal W b L).naturality f) ((toTime W b L).naturality f)

/-- Every chart still covers every vertex of the old coefficient. -/
theorem toOriginal_surjective (p : Index W b L) :
    Function.Surjective ((toOriginal W b L).app p).toOrderHom :=
  TimePrismChainDiagram.coeffProjection_surjective (coefficient W b L) (time W b L) p

private abbrev T (p : Index W b L) :=
  OrderedLabelElements.necklace W b ((oldLabels W b L).obj p)
private abbrev Y (p : Index W b L) :=
  (OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).obj (op (T W b L p))

/-- The actual old and realized labels agree on every simplex of the entire chosen chain. -/
theorem labels_restrict (p : Index W b L) :
    (Y W b L p).map ((toOriginal W b L).app p).op
      (OrderedLabelElements.label W b ((oldLabels W b L).obj p)) =
    (Y W b L p).map ((toRealized W b L).app p).op
      (OrderedLabelElements.label W b ((realizedLabels W b L).obj p)) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.yonedaEquiv_symm_map, SSet.yonedaEquiv_symm_map]
  let s := ((base W b L).obj p).unop.2.2
  change _ = SSet.stdSimplex.map ((toRealized W b L).app p) ≫
    SSet.yonedaEquiv.symm (SSet.yonedaEquiv s.val)
  rw [Equiv.symm_apply_apply]
  exact (chain_interior_fixed s ((toOriginal W b L).app p) ((toTime W b L).app p)).symm

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismChains
