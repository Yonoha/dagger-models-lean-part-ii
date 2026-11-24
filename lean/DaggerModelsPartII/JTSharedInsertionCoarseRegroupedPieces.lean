import DaggerModelsPartII.JTSharedInsertionCoarseCoalescedCoefficients
import DaggerModelsPartII.JTSharedInsertionCoarseRegroupedNative
import DaggerModelsPartII.JTSharedInsertionNativeAssembly

/-!
# Both actual grouped pieces factor through the original source before Q

Use the EXACT native transports of the complete coefficient comparisons.
Original source and cut frames are compared explicitly, before substituting
actual F,j. The right diagonal piece is handled by its native restriction;
no raw value, coefficient compatibility, constant row or section is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseRegroupedPieces

noncomputable section

private theorem dependent_congr {I : Sort*} {T : I → Sort*} (f : ∀ i, T i)
    {i j : I} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

private theorem left_change {T U : NecklaceCode} (hT : T = U)
    (a b : Fin (T.len + 1)) (a' b' : Fin (U.len + 1)) (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : HEq a a') (hb : HEq b b') :
    HEq (JTCorrectedIntervalAssembly.leftOver T a b hab).map
      (JTCorrectedIntervalAssembly.leftOver U a' b' hab').map := by
  subst U
  have ha' : a = a' := eq_of_heq ha
  have hb' : b = b' := eq_of_heq hb
  subst a'
  subst b'
  rfl

private def rightRestriction (T : NecklaceCode) (b c : Fin (T.len + 1)) (hbc : b ≤ c) :
    (JTCoarseRegroupingAssembly.correctedRight T c).code.toSSet ⟶ T.toSSet :=
  wedgeιRight (intervalOver.{0} T b c hbc).code
      (JTCoarseRegroupingAssembly.correctedRight T c).code ≫
    (JTCorrectedIntervalAssembly.rightOver T b c hbc).map

private theorem right_change {T U : NecklaceCode} (hT : T = U)
    (b c : Fin (T.len + 1)) (b' c' : Fin (U.len + 1)) (hbc : b ≤ c) (hbc' : b' ≤ c')
    (hb : HEq b b') (hc : HEq c c') :
    HEq (rightRestriction T b c hbc) (rightRestriction U b' c' hbc') := by
  subst U
  have hb' : b = b' := eq_of_heq hb
  have hc' : c = c' := eq_of_heq hc
  subst b'
  subst c'
  rfl

private theorem transported_native {P R : NecklaceCode} {X : SSet.{0}}
    (h : P = R) (f : R.toSSet ⟶ X) (g : P.toSSet ⟶ X) (hfg : HEq f g) :
    (eqToHom h : P ⟶ R).map ≫ f = g := by
  subst R
  have h' : f = g := eq_of_heq hfg
  exact (Category.id_comp f).trans h'

private theorem generic_left (T : NecklaceCode) (a c : Fin (T.len + 1)) (hac : a ≤ c) :
    (JTCorrectedIntervalAssembly.leftOver T a c hac).map =
      wedgeιLeft (JTCorrectedIntervalAssembly.leftOver T a c hac).code
          (JTCoarseRegroupingAssembly.correctedRight T c).code ≫
        (JTCoarseRegroupingAssembly.correctedGrouped T a c hac).map :=
  (JTCoarseRegroupingAssembly.corrected_left T a c hac).symm

private theorem generic_right (T : NecklaceCode) (a c : Fin (T.len + 1)) (hac : a ≤ c) :
    rightRestriction T c c le_rfl =
      wedgeιRight (JTCorrectedIntervalAssembly.leftOver T a c hac).code
          (JTCoarseRegroupingAssembly.correctedRight T c).code ≫
        (JTCoarseRegroupingAssembly.correctedGrouped T a c hac).map :=
  (JTCoarseRegroupingAssembly.diagonal_right T c).trans
    (JTCoarseRegroupingAssembly.corrected_right T a c hac).symm

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The unchanged actual shared-chain source. -/
abbrev Index := JTSharedInsertionChoices.Index F j

private abbrev M := JTExactlyMarkedSourceDiagram.Index F j
private abbrev rho := JTSharedInsertionCoarseCoalescedCoefficients.rho F j
private abbrev marks := JTSharedInsertionChainSupport.marks F j
private abbrev original := JTSharedInsertionChainSupport.originalBase F j
private abbrev pairs := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j
private abbrev T (p : Index F j) := (JTParametrizedTargetFamilies.codes L).obj ((pairs F j).obj p).1
private abbrev a (p : Index F j) := ((pairs F j).obj p).2.left.val
private abbrev c (p : Index F j) := ((pairs F j).obj p).2.right.val
private abbrev hac (p : Index F j) := ((pairs F j).obj p).2.le

private theorem pair_base (p : Index F j) : (original F j).obj p = ((pairs F j).obj p).1 := rfl
private theorem pair_left (p : Index F j) : (marks F j 0).obj p =
    (JTJointPairSourceDiagram.leftCut F j).obj ((pairs F j).obj p) := rfl
private theorem pair_right (p : Index F j) : (marks F j 2).obj p =
    (JTJointPairSourceDiagram.rightCut F j).obj ((pairs F j).obj p) := rfl

private theorem original_eq (p : Index F j) :
    (JTParametrizedTargetFamilies.codes L).obj ((original F j).obj (rho F j p)) = T F j p :=
  congrArg (JTParametrizedTargetFamilies.codes L).obj
    ((congrArg (fun G : Index F j ⥤ I ↦ G.obj p)
      (JTSharedInsertionCoarseCoalescence.rhoIndex_original F j)).trans (pair_base F j p))

private theorem marked0 (p : Index F j) : (marks F j 0).obj (rho F j p) =
    (JTJointPairSourceDiagram.leftCut F j).obj ((pairs F j).obj p) :=
  (congrArg (fun G : Index F j ⥤ M F j ↦ G.obj p)
    (JTSharedInsertionCoarseCoalescence.rhoIndex_earlier F j)).trans (pair_left F j p)

private theorem marked1 (p : Index F j) : (marks F j 1).obj (rho F j p) =
    (JTJointPairSourceDiagram.rightCut F j).obj ((pairs F j).obj p) :=
  (congrArg (fun G : Index F j ⥤ M F j ↦ G.obj p)
    (JTSharedInsertionCoarseCoalescence.rhoIndex_middle F j)).trans (pair_right F j p)

private theorem marked2 (p : Index F j) : (marks F j 2).obj (rho F j p) =
    (JTJointPairSourceDiagram.rightCut F j).obj ((pairs F j).obj p) :=
  (congrArg (fun G : Index F j ⥤ M F j ↦ G.obj p)
    (JTSharedInsertionCoarseCoalescence.rhoIndex_later F j)).trans (pair_right F j p)

private theorem left_view (p : Index F j) :
    HEq (JTSharedInsertionNativeAssembly.leftToOriginal F j (rho F j p))
      (JTCorrectedIntervalAssembly.leftOver (T F j p) (a F j p) (c F j p) (hac F j p)).map := by
  exact left_change (original_eq F j p) _ _ _ _ _ _
    (dependent_congr (fun m : M F j ↦ m.2.val) (marked0 F j p))
    (dependent_congr (fun m : M F j ↦ m.2.val) (marked1 F j p))

set_option maxHeartbeats 400000 in
private theorem right_view (p : Index F j) :
    HEq (wedgeιRight
        ((JTSharedInsertionSeamSurroundings.upperNative F j).obj (rho F j p))
        (wedge (single 1)
          ((JTParametrizedTargetFamilies.codes (JTActualJointChainSideLabels.rightLabels F j)).obj
            ((JTSharedInsertionChoices.laterChain F j).obj (rho F j p)))) ≫
      JTSharedInsertionNativeAssembly.rightToOriginal F j (rho F j p))
      (rightRestriction (T F j p) (c F j p) (c F j p) le_rfl) := by
  have h := right_change (original_eq F j p) _ _ _ _
    ((JTSharedInsertionChoices.projection F j).obj
      ((JTSharedInsertionChoices.base F j).obj (rho F j p))).2.property.2 le_rfl
    (dependent_congr (fun m : M F j ↦ m.2.val) (marked1 F j p))
    (dependent_congr (fun m : M F j ↦ m.2.val) (marked2 F j p))
  exact h

set_option maxHeartbeats 400000 in
/-- The EXACT full left native factor into the original source, BEFORE Q. -/
theorem left_factor (p : Index F j) :
    JTSharedInsertionCoarseCoalescedCoefficients.leftMap F j p ≫
        JTSharedInsertionNativeAssembly.leftToOriginal F j (rho F j p) =
      wedgeιLeft (JTSharedInsertionCoarseCoalescedCoefficients.leftCode F j p)
          (JTSharedInsertionCoarseCoalescedCoefficients.rightCode F j p) ≫
        (JTSharedInsertionCoarseRegroupedNative.groupedAssembly F j p).map := by
  have h := (left_view F j p).trans (heq_of_eq
    (generic_left (T F j p) (a F j p) (c F j p) (hac F j p)))
  have h' := transported_native
    (JTSharedInsertionCoarseCoalescedCoefficients.left_code_eq F j p) _ _ h
  exact h'

set_option maxHeartbeats 400000 in
/-- The EXACT restricted right native factor retains both later edges, BEFORE Q. -/
theorem right_factor (p : Index F j) :
    JTSharedInsertionCoarseCoalescedCoefficients.rightInclusion F j p ≫
        JTSharedInsertionNativeAssembly.rightToOriginal F j (rho F j p) =
      wedgeιRight (JTSharedInsertionCoarseCoalescedCoefficients.leftCode F j p)
          (JTSharedInsertionCoarseCoalescedCoefficients.rightCode F j p) ≫
        (JTSharedInsertionCoarseRegroupedNative.groupedAssembly F j p).map := by
  change ((eqToHom (JTSharedInsertionCoarseCoalescedCoefficients.right_code_eq F j p) :
      JTSharedInsertionCoarseCoalescedCoefficients.rightCode F j p ⟶ _).map ≫ _) ≫ _ = _
  rw [Category.assoc]
  have h := (right_view F j p).trans (heq_of_eq
    (generic_right (T F j p) (a F j p) (c F j p) (hac F j p)))
  have h' := transported_native
    (JTSharedInsertionCoarseCoalescedCoefficients.right_code_eq F j p) _ _ h
  exact h'

end
end DaggerModels.PartII.JTSharedInsertionCoarseRegroupedPieces
