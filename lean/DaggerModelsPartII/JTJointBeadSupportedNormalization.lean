import DaggerModelsPartII.JTSupportedNormalizedLabel
import DaggerModelsPartII.JTPrismJointOrderedLabel

/-! Both correction edges of an actual joint bead are stationary on its full support. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointBeadSupportedNormalization

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTMixedGraphEndpointLifts (rowVertex)
open JTParametrizedBeadGraph (beadLabel fullBeadSupport fullBeadSupportInclusion jointCoefficient)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)
open JTConstantOrderedLabel (constantCoefficient constantIndex constantLabel)
open OrderedNecklaceVertexPoints (zeroPoint)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev E := single 1

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ) (j : JTTargetJointMarks.Joint Q.code)
variable (r : (single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)

private abbrev native := r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j
private abbrev k := (JTJointRelativeGraphFamily.coefficient (L := L)).obj a
private abbrev l := fullBeadSupport F a d (native F a d j r)
private abbrev u := fullBeadSupportInclusion F a d (native F a d j r)
private abbrev z := jointCoefficient (Q := Q) j

/-- The unchanged old-degree native bead coefficient. -/
abbrev coefficient := SSet.yonedaEquiv.symm (beadLabel (a := a) d (native F a d j r))
private abbrev ρ := JTParametrizedBeadGraph.coefficient (a := a) d (native F a d j r)
private abbrev f₀ := ρ F a d j r ≫ rowVertex W ⦋d⦌ 0
private abbrev f₁ := ρ F a d j r ≫ rowVertex W ⦋d⦌ (Fin.last d)

private theorem row_label : ρ F a d j r ≫ JTNativeRowLabel.labelFromRow W d =
    coefficient F a d j r := by
  apply SSet.yonedaEquiv.injective
  simpa only [coefficient, Equiv.apply_symm_apply] using
    JTParametrizedBeadGraph.coefficient_label (a := a) d (native F a d j r)

private theorem first_row : coefficient F a d j r ≫ firstRestriction W (single d) =
    f₀ F a d j r ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  change coefficient F a d j r ≫ diagramMappingPrecomp
    (discreteFree.map (pointAt (single d) (ULift.up 0))) W = _
  rw [← row_label, Category.assoc, JTNativeRowLabel.labelFromRow_vertex]
  rfl

private theorem last_row : coefficient F a d j r ≫ lastRestriction W (single d) =
    f₁ F a d j r ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  change coefficient F a d j r ≫ diagramMappingPrecomp
    (discreteFree.map (pointAt (single d) (ULift.up (Fin.last d)))) W = _
  rw [← row_label, Category.assoc, JTNativeRowLabel.labelFromRow_vertex]
  rfl

/-- Only the full used face, rather than the whole old coefficient, is constant. -/
theorem coefficient_onSupport : std.map (u F a d j r) ≫ coefficient F a d j r =
    constantCoefficient W (z j) (single d) (l F a d j r) :=
  JTParametrizedBeadGraph.restrictedBeadLabel_at_joint F a d j r

private theorem first_row_onSupport :
    std.map (u F a d j r) ≫ f₀ F a d j r =
      term (std.obj (l F a d j r)) ≫ vertexPoint W (z j) := by
  haveI : Mono (TwoBeadEndpointLabel.jointLabelFromRow W) := by
    change Mono (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono (TwoBeadEndpointLabel.jointLabelFromRow W)).mp
  rw [Category.assoc, ← first_row, ← Category.assoc, coefficient_onSupport,
    ← JTConstantOrderedLabel.coefficient_constantLabel,
    JTOrderedLabelBinaryGlue.coefficient_first, Category.assoc,
    TwoBeadEndpointLabel.jointLabelFromRow_vertex]

private theorem last_row_onSupport :
    std.map (u F a d j r) ≫ f₁ F a d j r =
      term (std.obj (l F a d j r)) ≫ vertexPoint W (z j) := by
  haveI : Mono (TwoBeadEndpointLabel.jointLabelFromRow W) := by
    change Mono (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono (TwoBeadEndpointLabel.jointLabelFromRow W)).mp
  rw [Category.assoc, ← last_row, ← Category.assoc, coefficient_onSupport,
    ← JTConstantOrderedLabel.coefficient_constantLabel,
    JTOrderedLabelBinaryGlue.coefficient_last, Category.assoc,
    TwoBeadEndpointLabel.jointLabelFromRow_vertex]

/-- There are full-degree correcting edges stationary on the whole timed bead
support; the supported constant triple has actual arrows to this normalized
label and to the point label. This is an objectwise existence, not a chosen
natural family over all beads. -/
theorem exists_normalized_span
    (hW : letI : HomotopicalAlgebra.ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; HomotopicalAlgebra.IsFibrant W) :
    ∃ D : JTSupportedNormalizedLabel.Data W (single d) (k (L := L) a) (z j),
      D.middle = coefficient F a d j r ∧
      std.map (u F a d j r) ≫ JTComposedPrismLabels.coefficient
        (JTSupportedNormalizedLabel.coefficients D) =
          constantCoefficient W (z j) (wedge E (wedge (single d) E)) (l F a d j r) ∧
      Nonempty (constantIndex W (z j) (wedge E (wedge (single d) E)) (l F a d j r) ⟶
        JTComposedPrismLabels.index (JTSupportedNormalizedLabel.coefficients D)) ∧
      Nonempty (constantIndex W (z j) (wedge E (wedge (single d) E)) (l F a d j r) ⟶
        JTPointTargetEvaluationCone.pointLabel W (z j)) := by
  haveI : Mono (u F a d j r) := JTRowGraphParameterSupport.inclusion_mono _
  obtain ⟨D, hD, hf, hb⟩ := JTSupportedNormalizedLabel.exists_supported (z j)
    (u F a d j r) (coefficient F a d j r) (f₀ F a d j r) (f₁ F a d j r)
    (first_row F a d j r) (last_row F a d j r)
    (first_row_onSupport F a d j r) (last_row_onSupport F a d j r) hW
  have hm : std.map (u F a d j r) ≫ D.middle =
      constantCoefficient W (z j) (single d) (l F a d j r) := by
    rw [hD]
    exact coefficient_onSupport F a d j r
  exact ⟨D, hD, JTSupportedNormalizedLabel.coefficient_onFace D _ hm hf hb,
    ⟨JTSupportedNormalizedLabel.fromSupported D _ hm hf hb⟩,
    ⟨JTSupportedNormalizedLabel.supportedToPoint⟩⟩


/-- A supported normalization retains the actual old middle and both strict
stationarity equations, so it can be evaluated on the entire timed prism. -/
structure SupportedData where
  data : JTSupportedNormalizedLabel.Data W (single d) (k (L := L) a) (z j)
  middle_eq : data.middle = coefficient F a d j r
  front_onSupport : std.map (u F a d j r) ≫ data.front =
    constantCoefficient W (z j) E (l F a d j r)
  back_onSupport : std.map (u F a d j r) ≫ data.back =
    constantCoefficient W (z j) E (l F a d j r)

/-- Full-support normalized data exist for each original joint bead. -/
theorem nonempty_supportedData
    (hW : letI : HomotopicalAlgebra.ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; HomotopicalAlgebra.IsFibrant W) :
    Nonempty (SupportedData F a d j r) := by
  haveI : Mono (u F a d j r) := JTRowGraphParameterSupport.inclusion_mono _
  obtain ⟨D, hm, hf, hb⟩ := JTSupportedNormalizedLabel.exists_supported (z j)
    (u F a d j r) (coefficient F a d j r) (f₀ F a d j r) (f₁ F a d j r)
    (first_row F a d j r) (last_row F a d j r)
    (first_row_onSupport F a d j r) (last_row_onSupport F a d j r) hW
  exact ⟨⟨D, hm, hf, hb⟩⟩

/-- The retained middle of any such normalization has the exact old supported value. -/
theorem SupportedData.middle_onSupport (N : SupportedData F a d j r) :
    std.map (u F a d j r) ≫ N.data.middle =
      constantCoefficient W (z j) (single d) (l F a d j r) := by
  rw [N.middle_eq]
  exact coefficient_onSupport F a d j r

end
end DaggerModels.PartII.JTJointBeadSupportedNormalization
