import DaggerModelsPartII.JTRelativeLabelContraction
import DaggerModelsPartII.JTJointBeadSupportedNormalization

/-! Contract a normalized three-bead label without changing its old degree. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedNormalizedContraction

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open OrderedNecklaceVertexPoints (boundaryPoint)
open TripleBeadEndpointLabel (labels)
open OrderedNecklaceLabelDiagram (necklaceBoundaryRestriction)
open JTConstantOrderedLabel (constantCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev code (T : NecklaceCode) := wedge (single 1) (wedge T (single 1))

/-- Any supported three-bead normalization contracts at its unchanged old
coefficient degree, stationary on the whole support and the outer boundary. -/
theorem exists_prism {W : Source} {T : NecklaceCode} {k l : SimplexCategory}
    (z : Vertex W) (u : l ⟶ k) [Mono u]
    (D : JTSupportedNormalizedLabel.Data W T k z)
    (hm : std.map u ≫ D.middle = constantCoefficient W z T l)
    (hf : std.map u ≫ D.front = constantCoefficient W z (single 1) l)
    (hb : std.map u ≫ D.back = constantCoefficient W z (single 1) l)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    ∃ H : std.obj k ⊗ (Δ[1] : SSet.{0}) ⟶ labels W (code T),
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice (std.obj k) 0 ≫ H =
        JTComposedPrismLabels.coefficient (JTSupportedNormalizedLabel.coefficients D) ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice (std.obj k) 1 ≫ H =
        constantCoefficient W z (code T) k ∧
      (std.map u ⊗ₘ 𝟙 (Δ[1] : SSet.{0})) ≫ H =
        fst (std.obj l) (Δ[1] : SSet.{0}) ≫ constantCoefficient W z (code T) l ∧
      H ≫ (necklaceBoundaryRestriction W).app (op (code T)) =
        fst (std.obj k) (Δ[1] : SSet.{0}) ≫
          term (std.obj k) ≫ boundaryPoint W z z := by
  let C := JTSupportedNormalizedLabel.coefficients D
  have hpos : 0 < (code T).len := by
    change 0 < 1 + (T.len + 1)
    omega
  have hboundary : JTComposedPrismLabels.coefficient C ≫
      (necklaceBoundaryRestriction W).app (op (code T)) =
      term (std.obj k) ≫ boundaryPoint W z z := by
    have h := JTOrderedLabelBinaryGlue.coefficient_boundary W z z (code T) k
      (JTComposedPrismLabels.orderedPoint C)
    change JTOrderedLabelBinaryGlue.coefficient W z z (code T) k
      (JTComposedPrismLabels.orderedPoint C) ≫ _ = _ at h
    rw [JTOrderedLabelBinaryGlue.coefficient,
      JTComposedPrismLabels.orderedPoint_coefficient, Equiv.symm_apply_apply] at h
    exact h
  exact JTRelativeLabelContraction.exists_relative_label_prism W z (code T) u hW hpos
    (JTComposedPrismLabels.coefficient C) hboundary
    (JTSupportedNormalizedLabel.coefficient_onFace D u hm hf hb)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
  (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ) (j : Joint Q.code)
variable (r : (single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)

/-- Every actual supported bead normalization contracts after adding its two
exterior edges, including when the original bead has degree zero. -/
theorem exists_bead_prism
    (N : JTJointBeadSupportedNormalization.SupportedData F a d j r)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    ∃ H : std.obj ((JTJointRelativeGraphFamily.coefficient (L := L)).obj a) ⊗
        (Δ[1] : SSet.{0}) ⟶ labels W (code (single d)),
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice
          (std.obj ((JTJointRelativeGraphFamily.coefficient (L := L)).obj a)) 0 ≫ H =
        JTComposedPrismLabels.coefficient (JTSupportedNormalizedLabel.coefficients N.data) ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice
          (std.obj ((JTJointRelativeGraphFamily.coefficient (L := L)).obj a)) 1 ≫ H =
        constantCoefficient W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
          (code (single d)) ((JTJointRelativeGraphFamily.coefficient (L := L)).obj a) ∧
      (std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F a d
          (r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j)) ⊗ₘ
          𝟙 (Δ[1] : SSet.{0})) ≫ H =
        fst _ (Δ[1] : SSet.{0}) ≫
          constantCoefficient W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
            (code (single d))
            (JTParametrizedBeadGraph.fullBeadSupport F a d
              (r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j)) ∧
      H ≫ (necklaceBoundaryRestriction W).app (op (code (single d))) =
        fst _ (Δ[1] : SSet.{0}) ≫
          term _ ≫ boundaryPoint W
            (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
            (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  let i := r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j
  let u := JTParametrizedBeadGraph.fullBeadSupportInclusion F a d i
  haveI : Mono u := JTRowGraphParameterSupport.inclusion_mono _
  exact exists_prism (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) u N.data
    (JTJointBeadSupportedNormalization.SupportedData.middle_onSupport F a d j r N)
    N.front_onSupport N.back_onSupport hW

end
end DaggerModels.PartII.JTSupportedNormalizedContraction
