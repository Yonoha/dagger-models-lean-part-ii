import DaggerModelsPartII.JTOrderedLabelCoefficientPadding
import DaggerModelsPartII.JTOrderedLabelPaddingSpace
import DaggerModelsPartII.JTOrderedNecklaceLabelFibrancy

/-! Identify strict padded choices with the vertices of the full weak extension space. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingChoiceSpace

open JTOrderedLabelCoefficientPadding (choices choicesEquiv)
open JTOrderedLabelPaddingSpace (extensionSpace extension_mem_iff extensionVertex)
open JTOrderedNecklaceLabelFibrancy (orderedNecklaceLabels_isFibrant)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable {A : Type} [SmallCategory A] {W : Source}
variable {x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)}
private abbrev b := OrderedNecklaceVertexPoints.boundaryPoint W x y
variable (L : A ⥤ OrderedLabelElements.Index W (b (W := W) (x := x) (y := y)))
variable (p : A)

private abbrev T := OrderedLabelElements.necklace W (b (W := W) (x := x) (y := y)) (L.obj p)
private abbrev k := OrderedLabelElements.degree W (b (W := W) (x := x) (y := y)) (L.obj p)
private abbrev Y :=
  (OrderedNecklaceLabelDiagram.orderedNecklaceLabels W (b (W := W) (x := x) (y := y))).obj (op (T L p))
private abbrev z := OrderedLabelElements.label W (b (W := W) (x := x) (y := y)) (L.obj p)

/-- The full extension space of the actual label at one diagram object. -/
abbrev space : SSet.{0} := extensionSpace (Y L p) (k L p) (z L p)

/-- Restriction on actual padded simplices is precisely the fiber equation. -/
def vertices : (choices L).obj (op p) ≃ (space L p).obj (op ⦋0⦌) :=
  (choicesEquiv L p).trans {
    toFun := fun u ↦
      extensionVertex (Y L p) (k L p) (z L p) (SSet.yonedaEquiv.symm u.val) (by
        change SSet.stdSimplex.{0}.map (JTOrderedLabelCoefficientPadding.embedding (k L p)) ≫
          SSet.yonedaEquiv.symm u.val = SSet.yonedaEquiv.symm (z L p)
        exact (SSet.yonedaEquiv_symm_map
          (JTOrderedLabelCoefficientPadding.embedding (k L p)) u.val).symm.trans
            (congrArg SSet.yonedaEquiv.symm u.property))
    invFun := fun v ↦
      ⟨SSet.yonedaEquiv (SSet.ihom₀Equiv v.val), by
        have h : JTOrderedLabelPaddingSpace.embedding (k L p) ≫ SSet.ihom₀Equiv v.val =
            SSet.yonedaEquiv.symm (z L p) :=
          (extension_mem_iff (Y L p) (k L p) (z L p) (SSet.ihom₀Equiv v.val)).mp (by
            rw [Equiv.symm_apply_apply]
            exact v.property)
        apply SSet.yonedaEquiv.symm.injective
        rw [SSet.yonedaEquiv_symm_map, Equiv.symm_apply_apply]
        exact h⟩
    left_inv := fun v ↦ Subtype.ext (by
      change SSet.yonedaEquiv (SSet.ihom₀Equiv (SSet.ihom₀Equiv.symm
        (SSet.yonedaEquiv.symm v.val))) = v.val
      rw [SSet.ihom₀Equiv.apply_symm_apply, SSet.yonedaEquiv.apply_symm_apply])
    right_inv := fun v ↦ Subtype.ext (by
      change SSet.ihom₀Equiv.symm (SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (SSet.ihom₀Equiv v.val))) = v.val
      rw [SSet.yonedaEquiv.symm_apply_apply, SSet.ihom₀Equiv.symm_apply_apply])
  }

/-- For a positive-length native code the exact space of coefficient
extensions has weakly contractible Kan homotopy type. -/
theorem space_toPoint_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hT : 0 < (T L p).len) :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from (space L p)) := by
  letI : IsFibrant (Y L p) := orderedNecklaceLabels_isFibrant W hW _ _ hT
  exact JTOrderedLabelPaddingSpace.extensionSpace_toPoint_weak (Y L p) (k L p) (z L p)

end
end DaggerModels.PartII.JTOrderedLabelPaddingChoiceSpace
