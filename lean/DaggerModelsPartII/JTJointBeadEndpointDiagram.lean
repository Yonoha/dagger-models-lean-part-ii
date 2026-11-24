import DaggerModelsPartII.JTJointBeadOverlapDiagram
import DaggerModelsPartII.JTParametrizedBeadGraphTimeMapOperators
import DaggerModelsPartII.JTJointBeadSupportedNormalization

/-! Natural old-degree endpoint rows for the full overlap bead diagram. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointBeadEndpointDiagram

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)
open JTMixedGraphEndpointLifts (rowVertex)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)

variable {A B : Type} [SmallCategory A] [SmallCategory B]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (base : B ⥤ A) (D : B ⥤ SimplexCategory)
variable (h₀ : ∀ {a b : B} (f : a ⟶ b), (D.map f).toOrderHom 0 = 0)
variable (h₁ : ∀ {a b : B} (f : a ⟶ b),
  (D.map f).toOrderHom (Fin.last (D.obj a).len) = Fin.last (D.obj b).len)
variable (r : ∀ b : B, (NecklaceCode.single (D.obj b).len).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app (base.obj b)) j j le_rfl).toSSet)
private abbrev native (b : B) :=
  r b ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app (base.obj b)) j
variable (hr : ∀ {a b : B} (f : a ⟶ b),
  (NecklaceCode.singleIso (D.obj a).len).inv ≫ native F j base D r a ≫
    ((codes L).map (base.map f)).map =
  std.map (D.map f) ≫ (NecklaceCode.singleIso (D.obj b).len).inv ≫
    native F j base D r b)

/-- The unchanged old coefficient degree on the bead diagram. -/
abbrev oldDegrees := JTJointBeadOverlapDiagram.oldDegrees L base

/-- The row zero restriction at either original endpoint of the bead. -/
def endpointRow (b : B) (v : Fin ((D.obj b).len + 1)) :
    std.obj ((oldDegrees (L := L) base).obj b) ⟶ row W ⦋0⦌ :=
  JTParametrizedBeadGraph.coefficient (a := base.obj b) (D.obj b).len
    (native F j base D r b) ≫ rowVertex W (D.obj b) v

include hr in
private theorem endpointRow_map {a b : B} (f : a ⟶ b)
    (v : Fin ((D.obj a).len + 1)) (w : Fin ((D.obj b).len + 1))
    (hv : (D.map f).toOrderHom v = w) :
    std.map ((oldDegrees (L := L) base).map f) ≫ endpointRow F j base D r b w =
      endpointRow F j base D r a v := by
  let g := base.map f
  let u := D.map f
  let i := native F j base D r a
  let i' := native F j base D r b
  have hc := JTParametrizedBeadGraph.coefficient_map g (D.obj a).len i
  have hh := JTParametrizedBeadGraph.coefficient_horizontal
    (a := base.obj b) (i ≫ ((codes L).map g).map) i' u (hr f)
  have hv' : (Rows W).map u.op ≫ rowVertex W (D.obj a) v =
      rowVertex W (D.obj b) w := by
    unfold rowVertex
    rw [← (Rows W).map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    change (SimplexCategory.const ⦋0⦌ (D.obj a) v ≫ u) =
      SimplexCategory.const ⦋0⦌ (D.obj b) w
    rw [SimplexCategory.const_comp, hv]
  change std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map g) ≫
    (JTParametrizedBeadGraph.coefficient (a := base.obj b) (D.obj b).len i' ≫
      rowVertex W (D.obj b) w) =
    JTParametrizedBeadGraph.coefficient (a := base.obj a) (D.obj a).len i ≫
      rowVertex W (D.obj a) v
  change std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map g) ≫
      JTParametrizedBeadGraph.coefficient (a := base.obj b) (D.obj a).len
        (i ≫ ((codes L).map g).map) =
    JTParametrizedBeadGraph.coefficient (a := base.obj a) (D.obj a).len i at hc
  calc
    _ = std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map g) ≫
        (JTParametrizedBeadGraph.coefficient (a := base.obj b) (D.obj b).len i' ≫
          (Rows W).map u.op) ≫ rowVertex W (D.obj a) v := by
      rw [← hv']
      simp only [Category.assoc]
    _ = std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map g) ≫
        JTParametrizedBeadGraph.coefficient (a := base.obj b) (D.obj a).len
          (i ≫ ((codes L).map g).map) ≫ rowVertex W (D.obj a) v := by
      rw [hh]
    _ = _ := by rw [← Category.assoc, hc]

/-- The full first endpoint row is natural on the original coefficient degrees. -/
def firstRows : oldDegrees (L := L) base ⋙ std ⟶
    (Functor.const B).obj (row W ⦋0⦌) where
  app b := endpointRow F j base D r b 0
  naturality _ _ f := by
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact endpointRow_map F j base D r hr f 0 0 (h₀ f)

/-- The full last endpoint row is natural on the original coefficient degrees. -/
def lastRows : oldDegrees (L := L) base ⋙ std ⟶
    (Functor.const B).obj (row W ⦋0⦌) where
  app b := endpointRow F j base D r b (Fin.last (D.obj b).len)
  naturality _ _ f := by
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact endpointRow_map F j base D r hr f
      (Fin.last (D.obj _).len) (Fin.last (D.obj _).len) (h₁ f)

/-- The naturally varying full timed support face in the old degree. -/
abbrev incl : JTJointBeadOverlapDiagram.degrees F j base D r hr ⟶
    oldDegrees (L := L) base :=
  JTFullPrismSupportedDiagram.incl
    (JTJointBeadOverlapDiagram.originalParameter F j base D r hr)

theorem incl_mono (b : B) : Mono ((incl F j base D r hr).app b) :=
  JTRowGraphParameterSupport.inclusion_mono _

private abbrev labelCoefficient (b : B) :=
  JTJointBeadSupportedNormalization.coefficient F (base.obj b) (D.obj b).len j (r b)

private theorem row_label (b : B) :
    JTParametrizedBeadGraph.coefficient (a := base.obj b) (D.obj b).len
        (native F j base D r b) ≫
      JTNativeRowLabel.labelFromRow W (D.obj b).len = labelCoefficient F j base D r b := by
  apply SSet.yonedaEquiv.injective
  simpa only [labelCoefficient, JTJointBeadSupportedNormalization.coefficient,
    Equiv.apply_symm_apply] using
    JTParametrizedBeadGraph.coefficient_label (a := base.obj b) (D.obj b).len
      (native F j base D r b)

private theorem first_row (b : B) :
    labelCoefficient F j base D r b ≫
        TripleBeadEndpointLabel.firstRestriction W (NecklaceCode.single (D.obj b).len) =
      endpointRow F j base D r b 0 ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  simp only [TripleBeadEndpointLabel.firstRestriction]
  rw [← row_label, Category.assoc, JTNativeRowLabel.labelFromRow_vertex]
  rfl

private theorem last_row (b : B) :
    labelCoefficient F j base D r b ≫
        TripleBeadEndpointLabel.lastRestriction W (NecklaceCode.single (D.obj b).len) =
      endpointRow F j base D r b (Fin.last (D.obj b).len) ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  simp only [TripleBeadEndpointLabel.lastRestriction]
  rw [← row_label, Category.assoc, JTNativeRowLabel.labelFromRow_vertex]
  rfl

/-- The first old-degree endpoint row is the joint vertex on the full used support. -/
theorem firstRows_supported (b : B) :
    std.map ((incl F j base D r hr).app b) ≫ (firstRows F j base D h₀ r hr).app b =
      term (std.obj ((JTJointBeadOverlapDiagram.degrees F j base D r hr).obj b)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  haveI : Mono (TwoBeadEndpointLabel.jointLabelFromRow W) := by
    change Mono (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono (TwoBeadEndpointLabel.jointLabelFromRow W)).mp
  change std.map ((incl F j base D r hr).app b) ≫ endpointRow F j base D r b 0 ≫
      TwoBeadEndpointLabel.jointLabelFromRow W = _
  rw [← first_row, ← Category.assoc]
  change (std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F (base.obj b)
      (D.obj b).len (native F j base D r b)) ≫ labelCoefficient F j base D r b) ≫ _ = _
  rw [JTJointBeadSupportedNormalization.coefficient_onSupport]
  rw [← JTConstantOrderedLabel.coefficient_constantLabel,
    JTOrderedLabelBinaryGlue.coefficient_first, Category.assoc,
    TwoBeadEndpointLabel.jointLabelFromRow_vertex]
  rfl

/-- The last old-degree endpoint row is the joint vertex on the full used support. -/
theorem lastRows_supported (b : B) :
    std.map ((incl F j base D r hr).app b) ≫ (lastRows F j base D h₁ r hr).app b =
      term (std.obj ((JTJointBeadOverlapDiagram.degrees F j base D r hr).obj b)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  haveI : Mono (TwoBeadEndpointLabel.jointLabelFromRow W) := by
    change Mono (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono (TwoBeadEndpointLabel.jointLabelFromRow W)).mp
  change std.map ((incl F j base D r hr).app b) ≫
      endpointRow F j base D r b (Fin.last (D.obj b).len) ≫
        TwoBeadEndpointLabel.jointLabelFromRow W = _
  rw [← last_row, ← Category.assoc]
  change (std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F (base.obj b)
      (D.obj b).len (native F j base D r b)) ≫ labelCoefficient F j base D r b) ≫ _ = _
  rw [JTJointBeadSupportedNormalization.coefficient_onSupport]
  rw [← JTConstantOrderedLabel.coefficient_constantLabel,
    JTOrderedLabelBinaryGlue.coefficient_last, Category.assoc,
    TwoBeadEndpointLabel.jointLabelFromRow_vertex]
  rfl

end
end DaggerModels.PartII.JTJointBeadEndpointDiagram
