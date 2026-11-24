import DaggerModelsPartII.JTSharedInsertionCoarseRawData
import DaggerModelsPartII.JTSharedInsertionCoarseCoalescence

/-!
# The grouped coarse coefficient has the actual coalesced outer restrictions

All five complete coefficients come from the SAME tuple and full chain. Compare
both complete grouped restrictions with the existing outer coefficients at
(a,c,c), using strict native-code transport. The upper diagonal interval is
removed only by a native restriction. No raw value or constant row is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseCoalescedCoefficients

open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue glue_first glue_last
  glue_left glue_right)

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

private def orderedAt {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
    (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y) (p : I) :=
  JTOrderedLabelBinaryGlue.coefficient W x y ((JTParametrizedTargetFamilies.codes L).obj p)
    ((JTParametrizedTargetFamilyComparison.degrees L).obj p) (L.obj p).unop.2

private theorem orderedAt_comp {I J : Type} [SmallCategory I] [SmallCategory J]
    {W : Source} {x y : Vertex W} (G : I ⥤ J)
    (L : J ⥤ DecoratedNecklaceHomDiagram.Index W x y) (p : I) :
    HEq (orderedAt (G ⋙ L) p) (orderedAt L (G.obj p)) := HEq.rfl

private theorem dependent_congr {I : Sort*} {T : I → Sort*} (f : ∀ i, T i)
    {i j : I} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

private theorem ordered_roundtrip {W : Source} {x y : Vertex W}
    {P R : NecklaceCode} {k : SimplexCategory}
    (C : JTComposedPrismLabels.Coefficients W P R k x y) :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge P R) k
        (JTComposedPrismLabels.index C).unop.2 = JTComposedPrismLabels.coefficient C := by
  change SSet.yonedaEquiv.symm (JTRealizedLabelEndpoints.orderedLabel W x y _ k
    (JTComposedPrismLabels.orderedPoint C)) = _
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  exact Equiv.symm_apply_apply SSet.yonedaEquiv _

private theorem glue_heq {W : Source} {P P' R R' : NecklaceCode} {k : SimplexCategory}
    (hP : P = P') (hR : R = R')
    (a : std.obj k ⟶ labels W P) (b : std.obj k ⟶ labels W R)
    (a' : std.obj k ⟶ labels W P') (b' : std.obj k ⟶ labels W R')
    (j : a ≫ lastRestriction W P = b ≫ firstRestriction W R)
    (j' : a' ≫ lastRestriction W P' = b' ≫ firstRestriction W R')
    (ha : HEq a a') (hb : HEq b b') : HEq (glue W P R k a b j) (glue W P' R' k a' b' j') := by
  subst P'
  subst R'
  have ha' : a = a' := eq_of_heq ha
  have hb' : b = b' := eq_of_heq hb
  subst a'
  subst b'
  rfl

private theorem restrict_right {W : Source} {P R : NecklaceCode} {k : SimplexCategory}
    (a : std.obj k ⟶ labels W P) (b : std.obj k ⟶ labels W R)
    (h : a ≫ lastRestriction W P = b ≫ firstRestriction W R) :
    glue W P R k a b h ≫ pre W (wedgeιRight P R) = b :=
  glue_right _ _ _ _ _ _ _

private theorem coefficient_transport {W : Source} {P R : NecklaceCode} {k : SimplexCategory}
    (h : P = R) (a : std.obj k ⟶ labels W P) (b : std.obj k ⟶ labels W R)
    (hab : HEq a b) : a = b ≫ pre W (eqToHom h : P ⟶ R).map := by
  subst R
  change a = b ≫ pre W (𝟙 P.toSSet)
  rw [pre_id]
  exact (eq_of_heq hab).trans (Category.comp_id b).symm

private theorem gap_transport {J : Type} {W : Source} (K : J → SimplexCategory)
    (B : J → NecklaceCode) (c : ∀ p, std.obj (K p) ⟶ labels W (B p))
    {p q : J} (h : p = q) {k : SimplexCategory} (a : k ⟶ K p) (b : k ⟶ K q)
    (hab : HEq a b) : HEq (std.map a ≫ c p) (std.map b ≫ c q) := by
  subst q
  have h' : a = b := eq_of_heq hab
  subst b
  rfl

private def leftOf {W : Source} {A e B f D : NecklaceCode} {k : SimplexCategory}
    (C : JTCoarseCoefficientRegrouping.Data A e B f D W k) :=
  JTThreePieceCoefficientReassociation.rightCoefficient W A e B k C.a C.s C.b
    C.as_join C.sb_join

private def rightOf {W : Source} {A e B f D : NecklaceCode} {k : SimplexCategory}
    (C : JTCoarseCoefficientRegrouping.Data A e B f D W k) :=
  glue W f D k C.t C.d C.td_join

private theorem grouped_left {W : Source} {A e B f D : NecklaceCode} {k : SimplexCategory}
    (C : JTCoarseCoefficientRegrouping.Data A e B f D W k) :
    JTCoarseCoefficientRegrouping.groupedCoefficient C ≫
        pre W (wedgeιLeft (wedge A (wedge e B)) (wedge f D)) = leftOf C :=
  glue_left _ _ _ _ _ _ _

private theorem grouped_right {W : Source} {A e B f D : NecklaceCode} {k : SimplexCategory}
    (C : JTCoarseCoefficientRegrouping.Data A e B f D W k) :
    JTCoarseCoefficientRegrouping.groupedCoefficient C ≫
        pre W (wedgeιRight (wedge A (wedge e B)) (wedge f D)) = rightOf C :=
  glue_right _ _ _ _ _ _ _

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The original common shared-chain source. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- Change only the middle insertion coordinate, retaining the same tuple and full chain. -/
abbrev rho (p : Index F j) := (JTSharedInsertionCoarseCoalescence.rhoIndex F j).obj p

private abbrev E := single 1
private abbrev pair (p : Index F j) := (JTSharedInsertionCoarseChoice.toPairChain F j).obj p
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev C (p : Index F j) := JTSharedInsertionCoarseRawData.data F j p
private abbrev K (p : Index F j) := (JTSharedInsertionChoices.ordinals F j).obj p
private abbrev earlier (p : Index F j) := (JTSharedInsertionChoices.earlierChain F j).obj p
private abbrev later (p : Index F j) := (JTSharedInsertionChoices.laterChain F j).obj p

private theorem pair_earlier (p : Index F j) :
    (JTJointPairChainDiagram.earlier F j).obj (pair F j p) = earlier F j p := rfl
private theorem pair_later (p : Index F j) :
    (JTJointPairChainDiagram.later F j).obj (pair F j p) = later F j p := rfl

private abbrev outerLeft (p : Index F j) :=
  orderedAt (JTActualJointChainSideLabels.leftLabels F j) (earlier F j p)
private abbrev outerRight (p : Index F j) :=
  orderedAt (JTActualJointChainSideLabels.rightLabels F j) (later F j p)
private abbrev outerLeftCode (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes (JTActualJointChainSideLabels.leftLabels F j)).obj
    (earlier F j p)
private abbrev outerRightCode (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes (JTActualJointChainSideLabels.rightLabels F j)).obj
    (later F j p)
private abbrev lowerCode (p : Index F j) :=
  (JTSharedInsertionSeamSurroundings.lowerNative F j).obj p
private abbrev lowerCoefficient (p : Index F j) :=
  std.map ((JTSharedInsertionChoices.toOriginal F j).app p) ≫
    JTJointPairGapDiagram.coefficient F j ((JTSharedInsertionSeamSurroundings.lowerPairs F j).obj p)

private theorem a_heq (p : Index F j) : HEq (C F j p).a (outerLeft F j (rho F j p)) := by
  rw [JTSharedInsertionCoarseRawData.data_a, JTSharedInsertionCoarseLabels.data_left]
  exact (orderedAt_comp (JTJointPairChainDiagram.earlier F j)
    (JTActualJointChainSideLabels.leftLabels F j) (pair F j p)).trans
    (dependent_congr (orderedAt (JTActualJointChainSideLabels.leftLabels F j))
      ((pair_earlier F j p).trans
        (JTSharedInsertionCoarseCoalescence.earlier_chain_obj F j p).symm))

private theorem d_heq (p : Index F j) : HEq (C F j p).d (outerRight F j (rho F j p)) := by
  rw [JTSharedInsertionCoarseRawData.data_d, JTSharedInsertionCoarseLabels.data_right]
  exact (orderedAt_comp (JTJointPairChainDiagram.later F j)
    (JTActualJointChainSideLabels.rightLabels F j) (pair F j p)).trans
    (dependent_congr (orderedAt (JTActualJointChainSideLabels.rightLabels F j))
      ((pair_later F j p).trans
        (JTSharedInsertionCoarseCoalescence.later_chain_obj F j p).symm))

private theorem middle_coefficient (p : Index F j) :
    ((JTSharedInsertionCoarseLabels.family F j).data p).middle =
      JTComposedPrismLabels.coefficient
        (JTJointPairGapChainLabels.coefficients F j (pair F j p)) := by
  rw [JTSharedInsertionCoarseLabels.data_middle]
  exact ordered_roundtrip (JTJointPairGapChainLabels.coefficients F j (pair F j p))

/-- The entire starting coefficient is the SAME actual shared starting edge at a. -/
theorem s_starting (p : Index F j) : (C F j p).s =
    (JTSharedInsertionIncidentEdges.starting F j 0).app p ≫
      TwoBeadEndpointLabel.edgeLabelFromRow W := by
  rw [JTSharedInsertionCoarseRawData.data_s, middle_coefficient]
  have h := JTJointPairGapChainLabels.coefficient_front F j (pair F j p)
  exact h.trans (congrArg (· ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
    (JTSharedInsertionCoarseChoice.earlier_starting F j p))

/-- The WHOLE old interval coefficient is retained at the exact original common alpha. -/
theorem b_gap (p : Index F j) : (C F j p).b =
    JTJointPairGapChainLabels.gapCoefficient F j (pair F j p) := by
  rw [JTSharedInsertionCoarseRawData.data_b, middle_coefficient, Category.assoc, ← pre_comp]
  exact JTJointPairGapChainLabels.coefficient_interior F j (pair F j p)

/-- The entire ending coefficient is the SAME actual shared ending edge at c. -/
theorem t_ending (p : Index F j) : (C F j p).t =
    (JTSharedInsertionIncidentEdges.ending F j 2).app p ≫
      TwoBeadEndpointLabel.edgeLabelFromRow W := by
  rw [JTSharedInsertionCoarseRawData.data_t, middle_coefficient, Category.assoc, ← pre_comp]
  have h := JTJointPairGapChainLabels.coefficient_back F j (pair F j p)
  exact h.trans (congrArg (· ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
    (JTSharedInsertionCoarseChoice.later_ending F j p))

private theorem s_coalesced (p : Index F j) : (C F j p).s =
    (JTSharedInsertionIncidentEdges.starting F j 0).app (rho F j p) ≫
      TwoBeadEndpointLabel.edgeLabelFromRow W :=
  (s_starting F j p).trans (congrArg (· ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
    (JTSharedInsertionCoarseCoalescence.earlier_starting F j p).symm)

private theorem t_coalesced (p : Index F j) : (C F j p).t =
    (JTSharedInsertionIncidentEdges.ending F j 2).app (rho F j p) ≫
      TwoBeadEndpointLabel.edgeLabelFromRow W :=
  (t_ending F j p).trans (congrArg (· ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
    (JTSharedInsertionCoarseCoalescence.later_ending F j p).symm)

private theorem b_lower_heq (p : Index F j) : HEq (C F j p).b
    (lowerCoefficient F j (rho F j p)) := by
  rw [b_gap]
  exact gap_transport
    (fun q : JTJointPairSourceDiagram.Index F j ↦
      (JTJointRelativeGraphFamily.coefficient (L := L)).obj q.1)
    (JTJointPairGapDiagram.code F j) (JTJointPairGapDiagram.coefficient F j)
    (JTSharedInsertionCoarseCoalescence.lower_pair F j p).symm
    ((JTJointPairChainDiagram.toOriginal F j).app (pair F j p))
    ((JTSharedInsertionChoices.toOriginal F j).app (rho F j p))
    (heq_of_eq ((JTSharedInsertionCoarseChoice.toPairChain_toOriginal F j p).trans
      (JTSharedInsertionCoarseCoalescence.rhoIndex_toOriginal F j p).symm))

/-- The complete grouped left native code. -/
abbrev leftCode (p : Index F j) := wedge (JTSharedInsertionCoarseRawData.leftCode F j p)
  (wedge E (JTSharedInsertionCoarseRawData.intervalCode F j p))

/-- The remaining complete right correction and original corrected suffix. -/
abbrev rightCode (p : Index F j) := wedge E (JTSharedInsertionCoarseRawData.rightCode F j p)

private theorem a_code_eq (p : Index F j) : JTSharedInsertionCoarseRawData.leftCode F j p =
    outerLeftCode F j (rho F j p) :=
  congrArg (JTParametrizedTargetFamilies.codes (JTActualJointChainSideLabels.leftLabels F j)).obj
    ((pair_earlier F j p).trans
      (JTSharedInsertionCoarseCoalescence.earlier_chain_obj F j p).symm)

private theorem d_code_eq (p : Index F j) : JTSharedInsertionCoarseRawData.rightCode F j p =
    outerRightCode F j (rho F j p) :=
  congrArg (JTParametrizedTargetFamilies.codes (JTActualJointChainSideLabels.rightLabels F j)).obj
    ((pair_later F j p).trans
      (JTSharedInsertionCoarseCoalescence.later_chain_obj F j p).symm)

private theorem b_code_eq (p : Index F j) : JTSharedInsertionCoarseRawData.intervalCode F j p =
    lowerCode F j (rho F j p) :=
  congrArg (JTJointPairGapDiagram.native F j).obj
    (JTSharedInsertionCoarseCoalescence.lower_pair F j p).symm

/-- Strictly identify the complete left code with the coalesced actual left surrounding. -/
theorem left_code_eq (p : Index F j) : leftCode F j p =
    (JTSharedInsertionSeamSurroundings.leftNative F j).obj (rho F j p) :=
  congrArg₂ wedge (a_code_eq F j p) (congrArg (wedge E) (b_code_eq F j p))

/-- Strictly identify the remaining right code with its coalesced actual inner piece. -/
theorem right_code_eq (p : Index F j) : rightCode F j p =
    wedge E (outerRightCode F j (rho F j p)) :=
  congrArg (wedge E) (d_code_eq F j p)

/-- The exact left native transport used by the existing full left raw theorem. -/
def leftMap (p : Index F j) : (leftCode F j p).toSSet ⟶
    ((JTSharedInsertionSeamSurroundings.leftNative F j).obj (rho F j p)).toSSet :=
  (eqToHom (left_code_eq F j p) : leftCode F j p ⟶ _).map

/-- Restrict past ONLY the upper interval, without making its coefficient row constant. -/
def rightInclusion (p : Index F j) : (rightCode F j p).toSSet ⟶
    ((JTSharedInsertionSeamSurroundings.rightNative F j).obj (rho F j p)).toSSet :=
  (eqToHom (right_code_eq F j p) : rightCode F j p ⟶ _).map ≫
    wedgeιRight ((JTSharedInsertionSeamSurroundings.upperNative F j).obj (rho F j p))
      (wedge E (outerRightCode F j (rho F j p)))

/-- The complete grouped coefficient restricted to its left native piece. -/
def leftCoefficient (p : Index F j) := leftOf (C F j p)

/-- The complete grouped coefficient restricted to its remaining right native piece. -/
def rightCoefficient (p : Index F j) := rightOf (C F j p)

private theorem left_heq (p : Index F j) : HEq (leftCoefficient F j p)
    (JTSharedInsertionSeamSurroundings.leftCoefficient F j (rho F j p)) := by
  apply glue_heq (a_code_eq F j p) (congrArg (wedge E) (b_code_eq F j p))
  · exact a_heq F j p
  · apply glue_heq rfl (b_code_eq F j p)
    · exact heq_of_eq (s_coalesced F j p)
    · exact b_lower_heq F j p

private def rightRestricted (p : Index F j) :=
  JTSharedInsertionSeamSurroundings.rightCoefficient F j p ≫
    pre W (wedgeιRight ((JTSharedInsertionSeamSurroundings.upperNative F j).obj p)
      (wedge E (outerRightCode F j p)))

private theorem right_heq (p : Index F j) : HEq (rightCoefficient F j p)
    (rightRestricted F j (rho F j p)) := by
  unfold rightRestricted JTSharedInsertionSeamSurroundings.rightCoefficient
  change HEq (rightCoefficient F j p)
    (glue W ((JTSharedInsertionSeamSurroundings.upperNative F j).obj (rho F j p))
      (wedge E (outerRightCode F j (rho F j p))) (K F j (rho F j p)) _ _ _ ≫
        pre W (wedgeιRight
          ((JTSharedInsertionSeamSurroundings.upperNative F j).obj (rho F j p))
          (wedge E (outerRightCode F j (rho F j p)))))
  rw [restrict_right]
  apply glue_heq rfl (d_code_eq F j p)
  · exact heq_of_eq (t_coalesced F j p)
  · exact d_heq F j p

/-- The whole left coefficient is the coalesced outer coefficient by strict code transport. -/
theorem left_coefficient (p : Index F j) : leftCoefficient F j p =
    JTSharedInsertionSeamSurroundings.leftCoefficient F j (rho F j p) ≫ pre W (leftMap F j p) :=
  coefficient_transport (left_code_eq F j p) _ _ (left_heq F j p)

/-- The full right coefficient is exactly the native restriction of the coalesced outer one. -/
theorem right_coefficient (p : Index F j) : rightCoefficient F j p =
    JTSharedInsertionSeamSurroundings.rightCoefficient F j (rho F j p) ≫
      pre W (rightInclusion F j p) := by
  have h := coefficient_transport (right_code_eq F j p) _ _ (right_heq F j p)
  exact h.trans (by rw [rightRestricted, rightInclusion, pre_comp, Category.assoc])

/-- The FIRST whole grouped restriction is the checked actual left outer coefficient. -/
theorem grouped_left_coefficient (p : Index F j) :
    JTCoarseCoefficientRegrouping.groupedCoefficient (C F j p) ≫
        pre W (wedgeιLeft (leftCode F j p) (rightCode F j p)) =
      JTSharedInsertionSeamSurroundings.leftCoefficient F j (rho F j p) ≫
        pre W (leftMap F j p) :=
  (grouped_left (C F j p)).trans (left_coefficient F j p)

/-- The SECOND whole grouped restriction is the native right restriction of the actual outer one. -/
theorem grouped_right_coefficient (p : Index F j) :
    JTCoarseCoefficientRegrouping.groupedCoefficient (C F j p) ≫
        pre W (wedgeιRight (leftCode F j p) (rightCode F j p)) =
      JTSharedInsertionSeamSurroundings.rightCoefficient F j (rho F j p) ≫
        pre W (rightInclusion F j p) :=
  (grouped_right (C F j p)).trans (right_coefficient F j p)

end
end DaggerModels.PartII.JTSharedInsertionCoarseCoalescedCoefficients
