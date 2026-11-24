import DaggerModelsPartII.JTActualJointGapPrism
import DaggerModelsPartII.JTActualSourceJointSideEvaluation

/-!
# A timed relative interval between two cuts over the same joint

The entire old interval is kept. Its variable endpoint labels are attached
to two relative edges, each using the original time parameter at that cut.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointGapEvaluation

open JTParametrizedTargetFamilies (Family codes)
open OrderedNecklaceVertexPoints
open ReversalDiscreteFreeColimits
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue glue_left
  glue_right glue_first glue_last)
open JTActualJointGapPrism (coefficient_first coefficient_last parameter_first parameter_last)
open JTActualJointSideFamilies (leftCoefficients rightCoefficients leftEdge_onFace rightEdge_onFace)
open JTActualJointCutPrism (left_last right_first)
open JTActualSourceJointSideEvaluation (support)
open JTJointSideWhisker (edgeParameter edgeParameter_boundary edge_raw)
open JTComposedPrismLabels (Coefficients rawProduct rawProduct_glue_eq)
open JTTargetJointMarks (Joint)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

section ConstantPaste

variable {W : Source} {T U : NecklaceCode} {k : SimplexCategory} {I : SSet.{0}}

private theorem constantPaste
    (c : std.obj k ⟶ labels W T) (d : std.obj k ⟶ labels W U)
    (hc : c ≫ lastRestriction W T = d ≫ firstRestriction W U)
    (p : T.toSSet ⊗ I ⟶ J.obj k) (q : U.toSSet ⊗ I ⟶ J.obj k)
    (h : (pointAt T (ULift.up (Fin.last T.len)) ⊗ₘ 𝟙 I) ≫ p =
      (pointAt U (ULift.up 0) ⊗ₘ 𝟙 I) ≫ q)
    (e : (Δ[0] : SSet.{0}) ⟶ Raw W)
    (hl : rawProduct W p c = fst T.toSSet I ≫ term T.toSSet ≫ e)
    (hr : rawProduct W q d = fst U.toSSet I ≫ term U.toSSet ≫ e) :
    rawProduct W (JTComposedPrismLabels.parameter p q h) (glue W T U k c d hc) =
      fst (wedge T U).toSSet I ≫ term (wedge T U).toSSet ≫ e := by
  apply rawProduct_glue_eq c d hc p q h (term (wedge T U).toSSet ≫ e)
  · have he : wedgeιLeft.{0} T U ≫ term (wedge T U).toSSet = term T.toSSet :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    simpa only [← Category.assoc (wedgeιLeft T U), he] using hl
  · have he : wedgeιRight.{0} T U ≫ term (wedge T U).toSSet = term U.toSSet :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    simpa only [← Category.assoc (wedgeιRight T U), he] using hr

end ConstantPaste

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (j : Joint Q.code)
private abbrev T := (codes L).obj a
private abbrev k := (JTJointRelativeGraphFamily.coefficient (L := L)).obj a
private abbrev I := J.obj (time.obj a)
private abbrev z := jointCoefficient (Q := Q) j
variable (v w : Fin ((T (L := L) a).len + 1)) (h : v ≤ w)
variable (hv : orderMap (F.collapse.app a).map v = j.val)
variable (hw : orderMap (F.collapse.app a).map w = j.val)
variable (hW : Localization.localObject SegalLocalizers.localizingFamily W)

private abbrev B := JTActualJointGapPrism.code (L := L) a v w h
private abbrev middle := JTActualJointGapPrism.coefficient (L := L) a v w h
private abbrev p := JTActualJointGapPrism.parameter F a v w h
private abbrev leftSupport := support F a j v hv
private abbrev rightSupport := support F a j w hw
private abbrev lC := rightCoefficients F a j v (leftSupport F a j v hv) hW.1
private abbrev rC := leftCoefficients F a j w (rightSupport F a j w hw) hW.1
private abbrev front := (lC F a j v hv hW).left
private abbrev back := (rC F a j w hw hW).right
private abbrev firstTime := JTActualSourceJointSupport.timeParameter F a v
private abbrev lastTime := JTActualSourceJointSupport.timeParameter F a w

private theorem backJoin :
    middle (L := L) a v w h ≫ lastRestriction W (B a v w h) =
      back F a j w hw hW ≫ firstRestriction W E := by
  rw [coefficient_last, ← left_last (L := L) a w]
  exact (rC F a j w hw hW).seam

private abbrev insideCoefficient :=
  glue W (B (L := L) a v w h) E (k (L := L) a) (middle (L := L) a v w h)
    (back F a j w hw hW) (backJoin F a j v w h hw hW)

private theorem frontJoin :
    front F a j v hv hW ≫ lastRestriction W E =
      insideCoefficient F a j v w h hw hW ≫ firstRestriction W (wedge (B a v w h) E) := by
  rw [glue_first, coefficient_first, ← right_first (L := L) a v]
  exact (lC F a j v hv hW).seam

/-- The whole old interval with its two relative edges in one shared degree. -/
def coefficients : Coefficients W E (wedge (B (L := L) a v w h) E) (k (L := L) a) (z j) (z j) where
  left := front F a j v hv hW
  right := insideCoefficient F a j v w h hw hW
  seam := frontJoin F a j v w h hv hw hW
  first := (lC F a j v hv hW).first
  last := by
    rw [glue_last]
    exact (rC F a j w hw hW).last

private theorem backTimeJoin :
    (pointAt (B (L := L) a v w h) (ULift.up (Fin.last (B a v w h).len)) ⊗ₘ 𝟙 (I a)) ≫
      p F a v w h =
    (pointAt E (ULift.up 0) ⊗ₘ 𝟙 (I a)) ≫ edgeParameter (lastTime F a w) := by
  rw [parameter_last, edgeParameter_boundary]

private abbrev insideParameter :=
  JTComposedPrismLabels.parameter (p F a v w h) (edgeParameter (lastTime F a w))
    (backTimeJoin F a v w h)

private theorem frontTimeJoin :
    (pointAt E (ULift.up (Fin.last E.len)) ⊗ₘ 𝟙 (I a)) ≫ edgeParameter (firstTime F a v) =
    (pointAt (wedge (B (L := L) a v w h) E) (ULift.up 0) ⊗ₘ 𝟙 (I a)) ≫
      insideParameter F a v w h := by
  rw [edgeParameter_boundary, ← pointAt_first_left (B (L := L) a v w h) E]
  have h₁ := JTComposedPrismLabels.parameter_left (p F a v w h)
    (edgeParameter (lastTime F a w)) (backTimeJoin F a v w h)
  rw [← Category.id_comp (𝟙 (I a)), ← tensorHom_comp_tensorHom, Category.assoc]
  change firstTime F a v =
    (pointAt (B a v w h) (ULift.up 0) ⊗ₘ 𝟙 (I a)) ≫
      ((wedgeιLeft (B a v w h) E ⊗ₘ 𝟙 (I a)) ≫ insideParameter F a v w h)
  rw [show (wedgeιLeft (B a v w h) E ⊗ₘ 𝟙 (I a)) ≫ insideParameter F a v w h =
    p F a v w h from h₁]
  exact (parameter_first F a v w h).symm

/-- The full time parameter on the padded interval, retaining both endpoint time maps. -/
def parameter :
    (wedge E (wedge (B (L := L) a v w h) E)).toSSet ⊗ I (time := time) a ⟶
      J.obj (k (L := L) a) :=
  JTComposedPrismLabels.parameter (edgeParameter (firstTime F a v))
    (insideParameter F a v w h) (frontTimeJoin F a v w h)

private abbrev jointRaw : (Δ[0] : SSet.{0}) ⟶ Raw W :=
  SSet.yonedaEquiv.symm (rawVertex W (z j))

private theorem frontRaw :
    rawProduct W (edgeParameter (firstTime F a v)) (front F a j v hv hW) =
      fst E.toSSet (I a) ≫ term E.toSSet ≫ jointRaw j := by
  let S := leftSupport F a j v hv
  rw [show firstTime F a v = S.timeMap ≫ J.map S.inclusion from S.time_eq]
  exact edge_raw S.inclusion S.timeMap _ (rightEdge_onFace F a j v S hW.1)

private theorem backRaw :
    rawProduct W (edgeParameter (lastTime F a w)) (back F a j w hw hW) =
      fst E.toSSet (I a) ≫ term E.toSSet ≫ jointRaw j := by
  let S := rightSupport F a j w hw
  rw [show lastTime F a w = S.timeMap ≫ J.map S.inclusion from S.time_eq]
  exact edge_raw S.inclusion S.timeMap _ (leftEdge_onFace F a j w S hW.1)

/-- The whole padded time prism maps to the original joint, without a choice of joint trace. -/
theorem raw :
    rawProduct W (parameter F a v w h)
      (JTComposedPrismLabels.coefficient (coefficients F a j v w h hv hw hW)) =
    fst (wedge E (wedge (B (L := L) a v w h) E)).toSSet (I a) ≫
      term (wedge E (wedge (B a v w h) E)).toSSet ≫ jointRaw j := by
  apply constantPaste _ _ (frontJoin F a j v w h hv hw hW)
    _ _ (frontTimeJoin F a v w h) (jointRaw j)
  · exact frontRaw F a j v hv hW
  · exact constantPaste _ _ (backJoin F a j v w h hw hW) _ _ (backTimeJoin F a v w h)
      (jointRaw j) (JTActualJointGapPrism.raw_constant F a v w h j hv hw) (backRaw F a j w hw hW)

/-- The old interval includes into the padded interval as its literal middle. -/
def interior : (B (L := L) a v w h).toSSet ⟶ (wedge E (wedge (B a v w h) E)).toSSet :=
  wedgeιLeft (B a v w h) E ≫ wedgeιRight E (wedge (B a v w h) E)

/-- Recover the full original interval parameter by restricting to the middle. -/
theorem parameter_interior :
    (interior (L := L) a v w h ⊗ₘ 𝟙 (I a)) ≫ parameter F a v w h = p F a v w h := by
  unfold interior parameter
  rw [← Category.id_comp (𝟙 (I a)), ← tensorHom_comp_tensorHom,
    Category.assoc, JTComposedPrismLabels.parameter_right,
    JTComposedPrismLabels.parameter_left]

/-- Recover the full old coefficient by restricting to the same middle. -/
theorem coefficient_interior :
    JTComposedPrismLabels.coefficient (coefficients F a j v w h hv hw hW) ≫
      diagramMappingPrecomp (discreteFree.{0}.map (interior (L := L) a v w h)) W =
      middle (L := L) a v w h := by
  unfold interior
  rw [Functor.map_comp, diagramMappingPrecomp_comp, ← Category.assoc,
    JTComposedPrismLabels.coefficient, glue_right]
  change insideCoefficient F a j v w h hw hW ≫
    diagramMappingPrecomp (discreteFree.{0}.map (wedgeιLeft (B a v w h) E)) W = _
  exact glue_left _ _ _ _ _ _ _

/-- The actual evaluation at the original point of the raw realization. -/
def family :=
  JTComposedPrismLabelSingleton.family (JTPointTargetEvaluationCone.pointTarget W (z j))
    (coefficients F a j v w h hv hw hW) (JTOrderedLabelJointInsertion.toPoint _)
    (parameter F a v w h) (raw F a j v w h hv hw hW)

end
end DaggerModels.PartII.JTActualJointGapEvaluation
