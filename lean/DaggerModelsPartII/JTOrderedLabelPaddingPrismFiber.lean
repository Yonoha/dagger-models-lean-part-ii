import DaggerModelsPartII.JTOrderedLabelPaddingPrismDiagram

/-! The full mixed diagram uses the unchanged fixed-label face operators on each fiber. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismFiber

open JTOrderedLabelPaddingPrismDiagram (choices forget enlarged blockCoefficients mixed_map_val)
open JTOrderedLabelPaddingPrism (blocks)
open JTPaddedTimeOperators (pad)
open SemiSimplexCategory (toSimplexCategory)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable {A : Type} [SmallCategory A]
variable (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

private abbrev k (p : Aᵒᵖ) := OrderedLabelElements.degree W b (L.obj p.unop)
private abbrev P := OrderedLabelElements.projection W b
private abbrev ordered := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b

/-- On a fixed original label, restriction of a realization is exactly precomposition
with the ordered time face for that coefficient. -/
theorem map_val (p : Aᵒᵖ) {m n : SemiSimplexCategory} (j : m ⟶ n)
    (z : ((choices W b L).obj p).obj (op n)) :
    (((choices W b L).obj p).map j.op z).2.val =
      SSet.stdSimplex.map (JTCommonCoefficientParameter.map
        (𝟙 (pad (k W b L p))) (Category.id_comp (blocks (k W b L p)))
        (toSimplexCategory.map j) (SemiSimplexCategory.homEquiv j).injective) ≫ z.2.val := by
  have h := mixed_map_val W b L
    (show (p, op n) ⟶ (p, op m) from (𝟙 p, j.op)) z
  let F := blockCoefficients W b L
  have hc : (enlarged W b L).map (show (p.unop, m) ⟶ (p.unop, n) from (𝟙 _, j)) =
      JTCommonCoefficientParameter.map (𝟙 (pad (k W b L p)))
        (Category.id_comp (blocks (k W b L p))) (toSimplexCategory.map j)
        (SemiSimplexCategory.homEquiv j).injective := by
    change JTCommonCoefficientParameter.map (F.map (𝟙 p.unop)).left
      (Over.w (F.map (𝟙 p.unop))) (toSimplexCategory.map j)
      (SemiSimplexCategory.homEquiv j).injective = _
    rw [F.map_id]
    rfl
  have hNative : (ordered W b).map ((P W b).map (L.map (𝟙 p.unop))).1.op = 𝟙 _ := by
    rw [L.map_id, (P W b).map_id]
    change (ordered W b).map (𝟙 _) = _
    exact (ordered W b).map_id _
  change (((choices W b L).obj p).map j.op z).2.val =
    SSet.stdSimplex.map ((enlarged W b L).map
      (show (p.unop, m) ⟶ (p.unop, n) from (𝟙 _, j))) ≫ z.2.val ≫
        (ordered W b).map ((P W b).map (L.map (𝟙 p.unop))).1.op at h
  rw [hc, hNative] at h
  exact h.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _))

/-- The forgetful component keeps precisely the extension simplex of the chosen pair. -/
theorem forget_apply (p : Aᵒᵖ) (n : SemiSimplexCategory)
    (z : ((choices W b L).obj p).obj (op n)) :
    ((forget W b L).app p).app (op n) z = z.1 := rfl

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismFiber
