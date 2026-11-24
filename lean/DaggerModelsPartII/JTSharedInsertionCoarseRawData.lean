import DaggerModelsPartII.JTCoarseCoefficientRegrouping
import DaggerModelsPartII.JTSharedInsertionCoarseLabels

/-!
# Reconstruct the actual coarse ordered coefficient from five whole pieces

Split the complete middle coefficient along its actual native inclusions, then
recover it by the existing mapping-space pullbacks. All factory and ordered
coefficient calculations are sealed before substituting the original F,j.
This is coefficient data only: no raw equation, evaluation or section is added.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseRawData

open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue glue_left glue_right
  glue_first glue_last wedgeMappingPullback)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := ReversalDiscreteFreeColimits.discreteFree.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (free.map g) W

private theorem pre_comp (W : Source) {X Y Z : SSet.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    pre W (g ≫ h) = pre W h ≫ pre W g := by
  rw [pre, free.map_comp, diagramMappingPrecomp_comp]

private theorem pre_id (W : Source) (X : SSet.{0}) : pre W (𝟙 X) = 𝟙 _ := by
  rw [pre, free.map_id, diagramMappingPrecomp_id]

private theorem first_pre_left (W : Source) (P Q : NecklaceCode) :
    pre W (wedgeιLeft P Q) ≫ firstRestriction W P = firstRestriction W (wedge P Q) := by
  change pre W (wedgeιLeft P Q) ≫ pre W (pointAt P (ULift.up 0)) = _
  rw [← pre_comp, pointAt_first_left]
  rfl

private theorem last_pre_right (W : Source) (P Q : NecklaceCode) :
    pre W (wedgeιRight P Q) ≫ lastRestriction W Q = lastRestriction W (wedge P Q) := by
  change pre W (wedgeιRight P Q) ≫ pre W (pointAt Q (ULift.up (Fin.last Q.len))) = _
  rw [← pre_comp, pointAt_last_right]
  rfl

private theorem split_join (W : Source) (P Q : NecklaceCode) {k : SimplexCategory}
    (c : std.obj k ⟶ labels W (wedge P Q)) :
    (c ≫ pre W (wedgeιLeft P Q)) ≫ lastRestriction W P =
      (c ≫ pre W (wedgeιRight P Q)) ≫ firstRestriction W Q := by
  simp only [Category.assoc]
  congr 1
  change pre W (wedgeιLeft P Q) ≫ pre W (pointAt P (ULift.up (Fin.last P.len))) =
    pre W (wedgeιRight P Q) ≫ pre W (pointAt Q (ULift.up 0))
  rw [← pre_comp, ← pre_comp, wedge_comm]

private theorem split_glue (W : Source) (P Q : NecklaceCode) {k : SimplexCategory}
    (c : std.obj k ⟶ labels W (wedge P Q)) :
    glue W P Q k (c ≫ pre W (wedgeιLeft P Q)) (c ≫ pre W (wedgeιRight P Q))
      (split_join W P Q c) = c := by
  apply (wedgeMappingPullback W P Q).hom_ext
  · exact glue_left _ _ _ _ _ _ _
  · exact glue_right _ _ _ _ _ _ _

variable {W : Source} {A e B f D : NecklaceCode} {k : SimplexCategory} {x y : Vertex W}
variable (T : JTThreePieceLabelOperators.Data W A (wedge e (wedge B f)) D k x y)

private def inner := T.middle ≫ pre W (wedgeιRight e (wedge B f))

/-- Five whole maps are obtained by the actual middle-piece restrictions. -/
def factory : JTCoarseCoefficientRegrouping.Data A e B f D W k where
  a := T.left
  s := T.middle ≫ pre W (wedgeιLeft e (wedge B f))
  b := inner T ≫ pre W (wedgeιLeft B f)
  t := inner T ≫ pre W (wedgeιRight B f)
  d := T.right
  as_join := by
    rw [Category.assoc, first_pre_left]
    exact T.left_join
  sb_join := by
    simpa only [inner, Category.assoc, first_pre_left] using
      split_join W e (wedge B f) T.middle
  bt_join := split_join W B f (inner T)
  td_join := by
    rw [Category.assoc, last_pre_right, inner, Category.assoc, last_pre_right]
    exact T.right_join

private def innerGlued := glue W B f k (factory T).b (factory T).t (factory T).bt_join

/-- Reconstruct the ENTIRE inner coefficient, not merely its endpoint rows. -/
theorem inner_reconstructed : innerGlued T = inner T :=
  split_glue W B f (inner T)

private theorem middle_join : (factory T).s ≫ lastRestriction W e =
    innerGlued T ≫ firstRestriction W (wedge B f) := by
  rw [innerGlued, glue_first]
  exact (factory T).sb_join

private def middleGlued := glue W e (wedge B f) k (factory T).s (innerGlued T) (middle_join T)

/-- Reconstruct the complete original middle coefficient. -/
theorem middle_reconstructed : middleGlued T = T.middle := by
  apply (wedgeMappingPullback W e (wedge B f)).hom_ext
  · simp only [middleGlued, glue_left, factory]
  · simpa only [middleGlued, glue_right] using inner_reconstructed T

private theorem middle_right : middleGlued T ≫ lastRestriction W (wedge e (wedge B f)) =
    T.right ≫ firstRestriction W D := by
  rw [middleGlued, glue_last, innerGlued, glue_last]
  exact (factory T).td_join

private theorem left_middle : T.left ≫ lastRestriction W A =
    middleGlued T ≫ firstRestriction W (wedge e (wedge B f)) := by
  rw [middleGlued, glue_first]
  exact (factory T).as_join

/-- The regrouping source coefficient is exactly the existing complete three-piece coefficient. -/
theorem factory_source : JTCoarseCoefficientRegrouping.sourceCoefficient (factory T) =
    JTComposedPrismLabels.coefficient (JTThreePieceLabelOperators.coefficients T) := by
  change glue W A (wedge (wedge e (wedge B f)) D) k T.left
      (glue W (wedge e (wedge B f)) D k (middleGlued T) T.right (middle_right T))
      (by rw [glue_first]; exact left_middle T) =
    glue W A (wedge (wedge e (wedge B f)) D) k T.left
      (glue W (wedge e (wedge B f)) D k T.middle T.right T.right_join)
      (by rw [glue_first]; exact T.left_join)
  apply (wedgeMappingPullback W A (wedge (wedge e (wedge B f)) D)).hom_ext
  · simp only [glue_left]
  · simp only [glue_right]
    apply (wedgeMappingPullback W (wedge e (wedge B f)) D).hom_ext
    · simpa only [glue_left] using middle_reconstructed T
    · simp only [glue_right]

/-- The original ordered-point roundtrip retains the same WHOLE mapping-space coefficient. -/
theorem factory_ordered : JTCoarseCoefficientRegrouping.sourceCoefficient (factory T) =
    JTOrderedLabelBinaryGlue.coefficient W x y (JTCoarseCoefficientRegrouping.sourceCode A e B f D)
      k (JTThreePieceLabelOperators.index T).unop.2 := by
  rw [factory_source]
  change _ = SSet.yonedaEquiv.symm
    (JTRealizedLabelEndpoints.orderedLabel W x y _ k
      (JTComposedPrismLabels.orderedPoint (JTThreePieceLabelOperators.coefficients T)))
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  exact (Equiv.symm_apply_apply SSet.yonedaEquiv _).symm

private abbrev Point (W : Source) (x y : Vertex W) (N : NecklaceCode) (k : SimplexCategory) :=
  ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
    (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj (op N)).obj (op k)

private theorem ordered_transport (N : NecklaceCode)
    (hN : N = JTCoarseCoefficientRegrouping.sourceCode A e B f D)
    (u : Point W x y N k) (hu : HEq u (JTThreePieceLabelOperators.index T).unop.2) :
    JTCoarseCoefficientRegrouping.sourceCoefficient (factory T) ≫
        pre W (eqToHom hN : N ⟶ JTCoarseCoefficientRegrouping.sourceCode A e B f D).map =
      JTOrderedLabelBinaryGlue.coefficient W x y N k u := by
  subst N
  have h : u = (JTThreePieceLabelOperators.index T).unop.2 := eq_of_heq hu
  subst u
  change JTCoarseCoefficientRegrouping.sourceCoefficient (factory T) ≫
      pre W (𝟙 (JTCoarseCoefficientRegrouping.sourceCode A e B f D).toSSet) = _
  rw [pre_id]
  exact (Category.comp_id (JTCoarseCoefficientRegrouping.sourceCoefficient (factory T))).trans
    (factory_ordered T)

private theorem family_point_heq {I : Type} [SmallCategory I]
    {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory} {W : Source} {x y : Vertex W}
    (C : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y) P M R K) (p : I) :
    HEq ((C.labels.obj p).unop.2) ((JTThreePieceLabelOperators.index (C.data p)).unop.2) :=
  HEq.rfl

variable {I : Type} [SmallCategory I]
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The original shared insertion chain index. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The SAME complete corrected prefix. -/
abbrev leftCode (p : Index F j) := (JTSharedInsertionCoarseLabels.leftNative F j).obj p

/-- The literal whole old outside interval, with all zero/equal cases retained. -/
abbrev intervalCode (p : Index F j) := (JTJointPairGapChainLabels.oldNative F j).obj
  ((JTSharedInsertionCoarseChoice.toPairChain F j).obj p)

/-- The SAME complete corrected suffix. -/
abbrev rightCode (p : Index F j) := (JTSharedInsertionCoarseLabels.rightNative F j).obj p

/-- The unchanged full common coefficient ordinal. -/
abbrev degree (p : Index F j) := (JTSharedInsertionChoices.ordinals F j).obj p

private abbrev E := single 1
private abbrev actual (p : Index F j) := (JTSharedInsertionCoarseLabels.family F j).data p
private abbrev native (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes (JTSharedInsertionCoarseLabels.labels F j)).obj p

/-- The ACTUAL five complete coefficients, supplied by the existing coarse label itself. -/
def data (p : Index F j) : JTCoarseCoefficientRegrouping.Data
    (leftCode F j p) E (intervalCode F j p) E (rightCode F j p) W (degree F j p) :=
  factory (actual F j p)

/-- The first piece is the entire original corrected left coefficient. -/
theorem data_a (p : Index F j) : (data F j p).a = (actual F j p).left := rfl

/-- The starting piece is the exact first native restriction of the complete middle. -/
theorem data_s (p : Index F j) : (data F j p).s = (actual F j p).middle ≫
    pre W (wedgeιLeft E (wedge (intervalCode F j p) E)) := rfl

/-- The old interval piece is the exact nested middle restriction. -/
theorem data_b (p : Index F j) : (data F j p).b =
    ((actual F j p).middle ≫ pre W (wedgeιRight E (wedge (intervalCode F j p) E))) ≫
      pre W (wedgeιLeft (intervalCode F j p) E) := rfl

/-- The ending piece is the other exact nested middle restriction. -/
theorem data_t (p : Index F j) : (data F j p).t =
    ((actual F j p).middle ≫ pre W (wedgeιRight E (wedge (intervalCode F j p) E))) ≫
      pre W (wedgeιRight (intervalCode F j p) E) := rfl

/-- The last piece is the entire original corrected right coefficient. -/
theorem data_d (p : Index F j) : (data F j p).d = (actual F j p).right := rfl

/-- Exact reconstruction of the ACTUAL complete three-piece mapping-space coefficient. -/
theorem source_coefficient (p : Index F j) :
    JTCoarseCoefficientRegrouping.sourceCoefficient (data F j p) =
      JTComposedPrismLabels.coefficient (JTThreePieceLabelOperators.coefficients (actual F j p)) :=
  factory_source (actual F j p)

/-- The strict native-code identification is derived from the original label projection. -/
theorem code_eq (p : Index F j) : native F j p = JTCoarseCoefficientRegrouping.sourceCode
    (leftCode F j p) E (intervalCode F j p) E (rightCode F j p) :=
  congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_projection F j p)

/-- The complete original ordered coefficient, before raw realization. -/
def orderedCoefficient (p : Index F j) : std.obj (degree F j p) ⟶ labels W (native F j p) :=
  JTOrderedLabelBinaryGlue.coefficient W x y (native F j p) (degree F j p)
    ((JTSharedInsertionCoarseLabels.labels F j).obj p).unop.2

/-- Reconstruct that exact ordered coefficient through the strict native-code transport. -/
theorem source_ordered (p : Index F j) :
    JTCoarseCoefficientRegrouping.sourceCoefficient (data F j p) ≫
        pre W (eqToHom (code_eq F j p) : native F j p ⟶
          JTCoarseCoefficientRegrouping.sourceCode
            (leftCode F j p) E (intervalCode F j p) E (rightCode F j p)).map =
      orderedCoefficient F j p :=
  ordered_transport (actual F j p) (native F j p) (code_eq F j p)
    ((JTSharedInsertionCoarseLabels.labels F j).obj p).unop.2
    (family_point_heq (JTSharedInsertionCoarseLabels.family F j) p)

end
end DaggerModels.PartII.JTSharedInsertionCoarseRawData
