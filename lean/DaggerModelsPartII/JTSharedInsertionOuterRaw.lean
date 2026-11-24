import DaggerModelsPartII.JTSharedInsertionNativeAssembly
import DaggerModelsPartII.JTActualJointChainInverseFace
import DaggerModelsPartII.JTWhiskeredGraphRawTransport
import DaggerModelsPartII.JTWhiskeredGraphRaw
import DaggerModelsPartII.JTJointPaddedOverlapEvaluation

/-!
Exact raw equations for both corrected surroundings on the actual shared chain.
Only the literal original-time graph coordinate equation is required of a
source domain. All original interval pieces and both correction edges at each
outer mark are evaluated in the SAME original Q. No Family on a coefficient
product and no section of an ordinal projection is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionOuterRaw

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)
open TripleBeadEndpointLabel (labels glue)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map i) W
private abbrev E := single 1

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev I := JTSharedInsertionChoices.Index F j
private abbrev old (p : I F j) := (JTSharedInsertionChainSupport.originalBase F j).obj p
private abbrev T (p : I F j) := (codes L).obj (old F j p)
private abbrev K (p : I F j) := (JTSharedInsertionChoices.ordinals F j).obj p
private abbrev α (p : I F j) := (JTSharedInsertionChoices.toOriginal F j).app p
private abbrev target (p : I F j) := (F.collapse.app (old F j p)).map ≫ Q.map
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

private abbrev Compatible (p : I F j) (S : NecklaceCode)
    (n : S.toSSet ⟶ (T F j p).toSSet) (c : std.obj (K F j p) ⟶ labels W S) :=
  ∀ {X : SSet.{0}} (h : X ⟶ S.toSSet) (q : X ⟶ J.obj (K F j p))
    (t : X ⟶ J.obj (time.obj (old F j p))),
    q ≫ J.map (α F j p) = lift (h ≫ n) t ≫ F.parameter (old F j p) →
    lift h q ≫ realizedLabel S.toSSet W (K F j p) (SSet.yonedaEquiv c) =
      h ≫ n ≫ target F j p

private theorem coordinate_piece {X B C S I P : SSet.{0}}
    (h : X ⟶ B) (q : X ⟶ P) (t : X ⟶ I) (n : B ⟶ C)
    (r : C ⊗ I ⟶ P) (hq : q = lift (h ≫ n) t ≫ r)
    (i : S ⟶ B) (n' : S ⟶ C) (hi : i ≫ n = n') :
    pullback.fst h i ≫ q =
      lift (pullback.snd h i ≫ n') (pullback.fst h i ≫ t) ≫ r := by
  have hn : pullback.fst h i ≫ (h ≫ n) = pullback.snd h i ≫ n' := by
    rw [← Category.assoc, pullback.condition, Category.assoc, hi]
  rw [hq, ← Category.assoc, comp_lift, hn]

private theorem glue_compatible (p : I F j) {S U : NecklaceCode}
    (n : (wedge S U).toSSet ⟶ (T F j p).toSSet)
    (l : S.toSSet ⟶ (T F j p).toSSet) (r : U.toSSet ⟶ (T F j p).toSSet)
    (hnl : wedgeιLeft S U ≫ n = l) (hnr : wedgeιRight S U ≫ n = r)
    (c : std.obj (K F j p) ⟶ labels W S)
    (d : std.obj (K F j p) ⟶ labels W U)
    (hc : c ≫ TripleBeadEndpointLabel.lastRestriction W S =
      d ≫ TripleBeadEndpointLabel.firstRestriction W U)
    (hl : Compatible F j p S l c) (hr : Compatible F j p U r d) :
    Compatible F j p (wedge S U) n (glue W S U (K F j p) c d hc) := by
  intro X h q t hq
  apply JTWhiskeredGraphRaw.binary_raw W h q c d hc (n ≫ target F j p)
  · have hp : (pullback.fst h (wedgeιLeft S U) ≫ q) ≫ J.map (α F j p) =
        lift (pullback.snd h (wedgeιLeft S U) ≫ l)
          (pullback.fst h (wedgeιLeft S U) ≫ t) ≫ F.parameter (old F j p) := by
      rw [Category.assoc]
      exact coordinate_piece h (q ≫ J.map (α F j p)) t n
        (F.parameter (old F j p)) hq _ l hnl
    have ht : (pullback.snd h (wedgeιLeft S U) ≫ wedgeιLeft S U) ≫
        (n ≫ target F j p) = pullback.snd h (wedgeιLeft S U) ≫ l ≫ target F j p := by
      rw [Category.assoc, ← Category.assoc (wedgeιLeft S U), hnl]
    simpa only [Category.assoc] using (hl (pullback.snd h (wedgeιLeft S U))
        (pullback.fst h (wedgeιLeft S U) ≫ q)
        (pullback.fst h (wedgeιLeft S U) ≫ t) hp).trans ht.symm
  · have hp : (pullback.fst h (wedgeιRight S U) ≫ q) ≫ J.map (α F j p) =
        lift (pullback.snd h (wedgeιRight S U) ≫ r)
          (pullback.fst h (wedgeιRight S U) ≫ t) ≫ F.parameter (old F j p) := by
      rw [Category.assoc]
      exact coordinate_piece h (q ≫ J.map (α F j p)) t n
        (F.parameter (old F j p)) hq _ r hnr
    have ht : (pullback.snd h (wedgeιRight S U) ≫ wedgeιRight S U) ≫
        (n ≫ target F j p) = pullback.snd h (wedgeιRight S U) ≫ r ≫ target F j p := by
      rw [Category.assoc, ← Category.assoc (wedgeιRight S U), hnr]
    simpa only [Category.assoc] using (hr (pullback.snd h (wedgeιRight S U))
        (pullback.fst h (wedgeιRight S U) ≫ q)
        (pullback.fst h (wedgeιRight S U) ≫ t) hp).trans ht.symm

private theorem old_restriction (p : I F j) (S : NecklaceCode)
    (n : S.toSSet ⟶ (T F j p).toSSet) :
    Compatible F j p S n (std.map (α F j p) ≫
      JTActualJointCutPrism.originalCoefficient (L := L) (old F j p) ≫ pre W n) := by
  intro X h q t hq
  have hold : lift (fst (T F j p).toSSet (J.obj (time.obj (old F j p))))
      (F.parameter (old F j p)) ≫
        realizedLabel (T F j p).toSSet W _
          (SSet.yonedaEquiv (JTActualJointCutPrism.originalCoefficient
            (L := L) (old F j p))) =
      fst (T F j p).toSSet (J.obj (time.obj (old F j p))) ≫ target F j p := by
    simpa only [JTComposedPrismLabels.rawProduct, JTBinaryPrismRealization.realizeProduct,
      Category.assoc] using JTActualJointCutPrism.original_raw F (old F j p)
  exact JTWhiskeredGraphRawTransport.raw W _ _ _ _ hold h q (lift (h ≫ n) t)
    n (α F j p) _ rfl (lift_fst _ _) hq

private abbrev chain (which : Fin 3) : I F j ⥤ JTActualJointChoiceChainGraph.Index F j :=
  ![JTSharedInsertionChoices.earlierChain F j, JTSharedInsertionChoices.middleChain F j,
    JTSharedInsertionChoices.laterChain F j] which
private abbrev marked (which : Fin 3) (p : I F j) :=
  (JTSharedInsertionChainSupport.marks F j which).obj p
private abbrev v (which : Fin 3) (p : I F j) := (marked F j which p).2.val
private abbrev hv (which : Fin 3) (p : I F j) := (marked F j which p).2.property
private abbrev constant0 (p : I F j) : E.toSSet ⟶ (T F j p).toSSet :=
  term E.toSSet ≫ pointAt (T F j p) (ULift.up (v F j 0 p))
private abbrev faceParameter0 (p : I F j) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F (old F j p) j
    (JTActualSourceJointSupport.liftedOverlapVertex F (old F j p) j
      (v F j 0 p) (hv F j 0 p))

private theorem constant_target0 (p : I F j) :
    constant0 F j p ≫ target F j p =
      term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
  have hp : pointAt (T F j p) (ULift.up (v F j 0 p)) ≫
      (F.collapse.app (old F j p)).map = pointAt Q.code (ULift.up j.val) := by
    rw [pointAt_comp]
    exact congrArg (pointAt Q.code) (ULift.ext _ _ (hv F j 0 p))
  have hj := JTJointPaddedOverlapEvaluation.target_map (W := W) (Q := Q) j
  calc
    _ = term E.toSSet ≫ (pointAt (T F j p) (ULift.up (v F j 0 p)) ≫
        (F.collapse.app (old F j p)).map) ≫ Q.map := by
      simp only [constant0, target, Category.assoc]
    _ = term E.toSSet ≫ pointAt Q.code (ULift.up j.val) ≫ Q.map := by rw [hp]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun f ↦ term E.toSSet ≫ f) hj.symm

private theorem edge_factor0 (p : I F j) {X : SSet.{0}}
    (h : X ⟶ E.toSSet) (q : X ⟶ J.obj (K F j p))
    (t : X ⟶ J.obj (time.obj (old F j p)))
    (hq : q ≫ J.map (α F j p) =
      lift (h ≫ constant0 F j p) t ≫ F.parameter (old F j p)) :
    q ≫ J.map (α F j p) =
      (lift (h ≫ term E.toSSet) t ≫ faceParameter0 F j p) ≫
        J.map ((JTExactlyMarkedSourceDiagram.incl F j).app (marked F j 0 p)) := by
  rw [hq]
  calc
    _ = lift (h ≫ term E.toSSet) t ≫
        JTActualSourceJointSupport.timeParameter F (old F j p) (v F j 0 p) := by
      simp only [constant0, JTActualSourceJointSupport.timeParameter, ← Category.assoc,
        lift_map, Category.comp_id]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ lift (h ≫ term E.toSSet) t ≫ f)
          (JTActualSourceJointSupport.timeParameter_factor F (old F j p) j
            (v F j 0 p) (hv F j 0 p)).symm

private theorem ending_compatible0 (p : I F j) :
    Compatible F j p E (constant0 F j p)
      ((JTSharedInsertionIncidentEdges.ending F j 0).app p ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W) := by
  intro X h q t hq
  have he := edge_factor0 F j p h q t hq
  exact (JTActualJointChainInverseFace.ending_raw F j
    ((chain F j 0).obj p) h q
    (lift (h ≫ term E.toSSet) t ≫ faceParameter0 F j p) he).trans
      (by simpa only [Category.assoc] using
        congrArg (fun f ↦ h ≫ f) (constant_target0 F j p).symm)

private theorem starting_compatible0 (p : I F j) :
    Compatible F j p E (constant0 F j p)
      ((JTSharedInsertionIncidentEdges.starting F j 0).app p ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W) := by
  intro X h q t hq
  have he := edge_factor0 F j p h q t hq
  exact (JTActualJointChainInverseFace.starting_raw F j
    ((chain F j 0).obj p) h q
    (lift (h ≫ term E.toSSet) t ≫ faceParameter0 F j p) he).trans
      (by simpa only [Category.assoc] using
        congrArg (fun f ↦ h ≫ f) (constant_target0 F j p).symm)

private abbrev constant2 (p : I F j) : E.toSSet ⟶ (T F j p).toSSet :=
  term E.toSSet ≫ pointAt (T F j p) (ULift.up (v F j 2 p))
private abbrev faceParameter2 (p : I F j) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F (old F j p) j
    (JTActualSourceJointSupport.liftedOverlapVertex F (old F j p) j
      (v F j 2 p) (hv F j 2 p))

private theorem constant_target2 (p : I F j) :
    constant2 F j p ≫ target F j p =
      term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
  have hp : pointAt (T F j p) (ULift.up (v F j 2 p)) ≫
      (F.collapse.app (old F j p)).map = pointAt Q.code (ULift.up j.val) := by
    rw [pointAt_comp]
    exact congrArg (pointAt Q.code) (ULift.ext _ _ (hv F j 2 p))
  have hj := JTJointPaddedOverlapEvaluation.target_map (W := W) (Q := Q) j
  calc
    _ = term E.toSSet ≫ (pointAt (T F j p) (ULift.up (v F j 2 p)) ≫
        (F.collapse.app (old F j p)).map) ≫ Q.map := by
      simp only [constant2, target, Category.assoc]
    _ = term E.toSSet ≫ pointAt Q.code (ULift.up j.val) ≫ Q.map := by rw [hp]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun f ↦ term E.toSSet ≫ f) hj.symm

private theorem edge_factor2 (p : I F j) {X : SSet.{0}}
    (h : X ⟶ E.toSSet) (q : X ⟶ J.obj (K F j p))
    (t : X ⟶ J.obj (time.obj (old F j p)))
    (hq : q ≫ J.map (α F j p) =
      lift (h ≫ constant2 F j p) t ≫ F.parameter (old F j p)) :
    q ≫ J.map (α F j p) =
      (lift (h ≫ term E.toSSet) t ≫ faceParameter2 F j p) ≫
        J.map ((JTExactlyMarkedSourceDiagram.incl F j).app (marked F j 2 p)) := by
  rw [hq]
  calc
    _ = lift (h ≫ term E.toSSet) t ≫
        JTActualSourceJointSupport.timeParameter F (old F j p) (v F j 2 p) := by
      simp only [constant2, JTActualSourceJointSupport.timeParameter, ← Category.assoc,
        lift_map, Category.comp_id]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ lift (h ≫ term E.toSSet) t ≫ f)
          (JTActualSourceJointSupport.timeParameter_factor F (old F j p) j
            (v F j 2 p) (hv F j 2 p)).symm

private theorem ending_compatible2 (p : I F j) :
    Compatible F j p E (constant2 F j p)
      ((JTSharedInsertionIncidentEdges.ending F j 2).app p ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W) := by
  intro X h q t hq
  have he := edge_factor2 F j p h q t hq
  exact (JTActualJointChainInverseFace.ending_raw F j
    ((chain F j 2).obj p) h q
    (lift (h ≫ term E.toSSet) t ≫ faceParameter2 F j p) he).trans
      (by simpa only [Category.assoc] using
        congrArg (fun f ↦ h ≫ f) (constant_target2 F j p).symm)

private theorem starting_compatible2 (p : I F j) :
    Compatible F j p E (constant2 F j p)
      ((JTSharedInsertionIncidentEdges.starting F j 2).app p ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W) := by
  intro X h q t hq
  have he := edge_factor2 F j p h q t hq
  exact (JTActualJointChainInverseFace.starting_raw F j
    ((chain F j 2).obj p) h q
    (lift (h ≫ term E.toSSet) t ≫ faceParameter2 F j p) he).trans
      (by simpa only [Category.assoc] using
        congrArg (fun f ↦ h ≫ f) (constant_target2 F j p).symm)

private abbrev insertion (p : I F j) :=
  (JTSharedInsertionChoices.projection F j).obj ((JTSharedInsertionChoices.base F j).obj p)
private abbrev hab (p : I F j) := (insertion F j p).2.property.1
private abbrev hbc (p : I F j) := (insertion F j p).2.property.2
private abbrev edgeOver0 (p : I F j) :=
  JTCorrectedIntervalAssembly.constantOver E
    ((T F j p).verticesEquiv.symm (ULift.up (v F j 0 p)))
private abbrev edgeOver2 (p : I F j) :=
  JTCorrectedIntervalAssembly.constantOver E
    ((T F j p).verticesEquiv.symm (ULift.up (v F j 2 p)))
private abbrev prefixOver (p : I F j) :=
  intervalOver (T F j p) 0 (v F j 0 p) (Fin.zero_le _)
private abbrev lowerOver (p : I F j) :=
  intervalOver (T F j p) (v F j 0 p) (v F j 1 p) (hab F j p)
private abbrev upperOver (p : I F j) :=
  intervalOver (T F j p) (v F j 1 p) (v F j 2 p) (hbc F j p)
private abbrev suffixOver (p : I F j) :=
  intervalOver (T F j p) (v F j 2 p) (Fin.last (T F j p).len) (Fin.le_last _)
private abbrev leftOuterOver (p : I F j) :=
  NecklacesOver.wedge (prefixOver F j p) (edgeOver0 F j p)
private abbrev leftInnerOver (p : I F j) :=
  NecklacesOver.wedge (edgeOver0 F j p) (lowerOver F j p)
private abbrev rightOuterOver (p : I F j) :=
  NecklacesOver.wedge (edgeOver2 F j p) (suffixOver F j p)
private abbrev rightInnerOver (p : I F j) :=
  NecklacesOver.wedge (edgeOver2 F j p) (rightOuterOver F j p)

private theorem corrected_left (p : I F j) :
    Compatible F j p (leftOuterOver F j p).code (leftOuterOver F j p).map
      (JTOrderedLabelBinaryGlue.coefficient W x (z j) _ (K F j p)
        ((JTActualJointChainSideLabels.leftLabels F j).obj
          ((JTSharedInsertionChoices.earlierChain F j).obj p)).unop.2) := by
  change Compatible F j p _ _
    (JTOrderedLabelBinaryGlue.coefficient W x (z j) _ _
      (JTComposedPrismLabels.orderedPoint
        (JTActualJointChainSideLabels.leftCoefficients F j
          ((JTSharedInsertionChoices.earlierChain F j).obj p))))
  rw [JTOrderedLabelBinaryGlue.coefficient, JTComposedPrismLabels.orderedPoint_coefficient,
    Equiv.symm_apply_apply]
  apply glue_compatible F j p (leftOuterOver F j p).map
    (prefixOver F j p).map (edgeOver0 F j p).map
    (NecklacesOver.wedge_left _ _) (NecklacesOver.wedge_right _ _)
  · exact old_restriction F j p _ _
  · exact ending_compatible0 F j p

private theorem corrected_right (p : I F j) :
    Compatible F j p (rightOuterOver F j p).code (rightOuterOver F j p).map
      (JTOrderedLabelBinaryGlue.coefficient W (z j) y _ (K F j p)
        ((JTActualJointChainSideLabels.rightLabels F j).obj
          ((JTSharedInsertionChoices.laterChain F j).obj p)).unop.2) := by
  change Compatible F j p _ _
    (JTOrderedLabelBinaryGlue.coefficient W (z j) y _ _
      (JTComposedPrismLabels.orderedPoint
        (JTActualJointChainSideLabels.rightCoefficients F j
          ((JTSharedInsertionChoices.laterChain F j).obj p))))
  rw [JTOrderedLabelBinaryGlue.coefficient, JTComposedPrismLabels.orderedPoint_coefficient,
    Equiv.symm_apply_apply]
  apply glue_compatible F j p (rightOuterOver F j p).map
    (edgeOver2 F j p).map (suffixOver F j p).map
    (NecklacesOver.wedge_left _ _) (NecklacesOver.wedge_right _ _)
  · exact starting_compatible2 F j p
  · exact old_restriction F j p _ _

/-- The full corrected left surrounding has its exact original-Q raw value on
any domain with the literal original coefficient/time coordinate equation. -/
theorem left_raw (p : I F j) {X : SSet.{0}}
    (h : X ⟶ ((JTSharedInsertionSeamSurroundings.leftNative F j).obj p).toSSet)
    (q : X ⟶ J.obj (K F j p)) (t : X ⟶ J.obj (time.obj (old F j p)))
    (hq : q ≫ J.map (α F j p) =
      lift (h ≫ JTSharedInsertionNativeAssembly.leftToOriginal F j p) t ≫
        F.parameter (old F j p)) :
    lift h q ≫ realizedLabel _ W (K F j p)
        (SSet.yonedaEquiv (JTSharedInsertionSeamSurroundings.leftCoefficient F j p)) =
      h ≫ JTSharedInsertionNativeAssembly.leftToOriginal F j p ≫
        (F.collapse.app (old F j p)).map ≫ Q.map := by
  have hc : Compatible F j p _
      (JTSharedInsertionNativeAssembly.leftToOriginal F j p)
      (JTSharedInsertionSeamSurroundings.leftCoefficient F j p) := by
    apply glue_compatible F j p (JTSharedInsertionNativeAssembly.leftToOriginal F j p)
      (leftOuterOver F j p).map (leftInnerOver F j p).map
      (NecklacesOver.wedge_left (leftOuterOver F j p) (leftInnerOver F j p))
      (NecklacesOver.wedge_right (leftOuterOver F j p) (leftInnerOver F j p))
    · exact corrected_left F j p
    · apply glue_compatible F j p (leftInnerOver F j p).map
        (edgeOver0 F j p).map (lowerOver F j p).map
        (NecklacesOver.wedge_left (edgeOver0 F j p) (lowerOver F j p))
        (NecklacesOver.wedge_right (edgeOver0 F j p) (lowerOver F j p))
      · exact starting_compatible0 F j p
      · exact old_restriction F j p _ _
  exact hc h q t hq

/-- The full corrected right surrounding retains both actual later correction
edges and the entire original suffix in its exact original-Q raw equation. -/
theorem right_raw (p : I F j) {X : SSet.{0}}
    (h : X ⟶ ((JTSharedInsertionSeamSurroundings.rightNative F j).obj p).toSSet)
    (q : X ⟶ J.obj (K F j p)) (t : X ⟶ J.obj (time.obj (old F j p)))
    (hq : q ≫ J.map (α F j p) =
      lift (h ≫ JTSharedInsertionNativeAssembly.rightToOriginal F j p) t ≫
        F.parameter (old F j p)) :
    lift h q ≫ realizedLabel _ W (K F j p)
        (SSet.yonedaEquiv (JTSharedInsertionSeamSurroundings.rightCoefficient F j p)) =
      h ≫ JTSharedInsertionNativeAssembly.rightToOriginal F j p ≫
        (F.collapse.app (old F j p)).map ≫ Q.map := by
  have hc : Compatible F j p _
      (JTSharedInsertionNativeAssembly.rightToOriginal F j p)
      (JTSharedInsertionSeamSurroundings.rightCoefficient F j p) := by
    apply glue_compatible F j p (JTSharedInsertionNativeAssembly.rightToOriginal F j p)
      (upperOver F j p).map (rightInnerOver F j p).map
      (NecklacesOver.wedge_left (upperOver F j p) (rightInnerOver F j p))
      (NecklacesOver.wedge_right (upperOver F j p) (rightInnerOver F j p))
    · exact old_restriction F j p _ _
    · apply glue_compatible F j p (rightInnerOver F j p).map
        (edgeOver2 F j p).map (rightOuterOver F j p).map
        (NecklacesOver.wedge_left (edgeOver2 F j p) (rightOuterOver F j p))
        (NecklacesOver.wedge_right (edgeOver2 F j p) (rightOuterOver F j p))
      · exact ending_compatible2 F j p
      · exact corrected_right F j p
  exact hc h q t hq

end
end DaggerModels.PartII.JTSharedInsertionOuterRaw
