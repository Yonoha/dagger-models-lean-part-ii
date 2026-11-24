import DaggerModelsPartII.JTOrderedLabelPaddingDiagram
import DaggerModelsPartII.JTOrderedLabelPaddingChoiceSpace

/-! The strict padded choices are naturally the vertices of the padded extension diagram. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTOrderedLabelPaddingVertices

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private theorem restriction_zero (W : Source)
    (β : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    {i j : OrderedLabelElements.Index W β} (f : i ⟶ j)
    (v : (JTOrderedLabelPaddingDiagram.fiberAt W β j).obj (op ⦋0⦌)) :
    SSet.ihom₀Equiv (((JTOrderedLabelPaddingDiagram.restriction W β f).app (op ⦋0⦌) v).val) =
      SSet.stdSimplex.map
          (JTPaddedTimeOperators.functor.map ((OrderedLabelElements.projection W β).map f).2) ≫
        (SSet.ihom₀Equiv v.val ≫
          ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W β).map
            ((OrderedLabelElements.projection W β).map f).1.op)) := by
  apply SSet.ihom₀Equiv.symm.injective
  rw [Equiv.symm_apply_apply, ← Category.assoc, SSet.ihom₀Equiv_symm_comp',
    SSet.ihom₀Equiv_symm_comp, Equiv.symm_apply_apply]
  exact congrFun
    (NatTrans.congr_app (JTOrderedLabelPaddingDiagram.restriction_ι W β f) (op ⦋0⦌)) v

variable {A : Type} [SmallCategory A] {W : Source}
variable {x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)}

private abbrev b := OrderedNecklaceVertexPoints.boundaryPoint W x y

variable (L : A ⥤ OrderedLabelElements.Index W (b (W := W) (x := x) (y := y)))

/-- The pointwise equivalence between strict padded choices and extension vertices
commutes with every original ordered-label operator. -/
theorem vertices_natural {p q : Aᵒᵖ} (f : p ⟶ q)
    (u : (JTOrderedLabelCoefficientPadding.choices L).obj p) :
    JTOrderedLabelPaddingChoiceSpace.vertices L q.unop
        ((JTOrderedLabelCoefficientPadding.choices L).map f u) =
      ((JTOrderedLabelPaddingDiagram.along W (b (W := W) (x := x) (y := y)) L ⋙
        SSet.evaluation.obj (op ⦋0⦌)).map f)
          (JTOrderedLabelPaddingChoiceSpace.vertices L p.unop u) := by
  change JTOrderedLabelPaddingChoiceSpace.vertices L q.unop
      ((JTOrderedLabelCoefficientPadding.choices L).map f u) =
    (JTOrderedLabelPaddingDiagram.restriction W (b (W := W) (x := x) (y := y))
      (L.map f.unop)).app (op ⦋0⦌)
        (JTOrderedLabelPaddingChoiceSpace.vertices L p.unop u)
  apply Subtype.ext
  apply SSet.ihom₀Equiv.injective
  rw [restriction_zero]
  change SSet.yonedaEquiv.symm
      (((JTOrderedLabelCoefficientPadding.choices L).map f u).val) =
    SSet.stdSimplex.map
        (JTPaddedTimeOperators.functor.map
          ((OrderedLabelElements.projection W (b (W := W) (x := x) (y := y))).map
            (L.map f.unop)).2) ≫
      (SSet.yonedaEquiv.symm u.val ≫
        (OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
          (b (W := W) (x := x) (y := y))).map
            ((OrderedLabelElements.projection W (b (W := W) (x := x) (y := y))).map
              (L.map f.unop)).1.op)
  rw [SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_map]
  rfl

end

end DaggerModels.PartII.JTOrderedLabelPaddingVertices
