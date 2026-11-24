import DaggerModelsPartII.JTSharedInsertionCoarseRawData
import DaggerModelsPartII.JTSharedInsertionCoarseRegroupedNative

/-!
# The complete ACTUAL coarse coefficient under native regrouping

Compose the checked actual ordered-coefficient reconstruction with the checked
five-piece coefficient reassociation. The same native map already commutes with
the whole original assembly BEFORE Q. No new compatibility premise is supplied.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseRegroupedCoefficient

noncomputable section

private theorem native_view (T : NecklaceCode) (a c : Fin (T.len + 1)) (hac : a ≤ c)
    (N : NecklaceCode)
    (e : N = (JTCorrectedCoarseIntervalComparison.coarseOver T a c hac).code) :
    eqToHom e ≫ (JTCoarseCoefficientRegrouping.deltaCodeIso
      (wedge (intervalOver.{0} T 0 a (Fin.zero_le a)).code (single 1)) (single 1)
      (intervalOver.{0} T a c hac).code (single 1)
      (wedge (single 1) (intervalOver.{0} T c (Fin.last T.len) (Fin.le_last c)).code)).hom =
      eqToHom e ≫ (JTCoarseRegroupingAssembly.correctedRegroup T a c hac).hom := rfl

private theorem native_transport (T : NecklaceCode) (a c : Fin (T.len + 1))
    (hac : a ≤ c) (A B D N : NecklaceCode)
    (hA : A = wedge (intervalOver.{0} T 0 a (Fin.zero_le a)).code (single 1))
    (hB : B = (intervalOver.{0} T a c hac).code)
    (hD : D = wedge (single 1) (intervalOver.{0} T c (Fin.last T.len) (Fin.le_last c)).code)
    (e : N = JTCoarseCoefficientRegrouping.sourceCode A (single 1) B (single 1) D)
    (e' : N = (JTCorrectedCoarseIntervalComparison.coarseOver T a c hac).code) :
    HEq (eqToHom e ≫ (JTCoarseCoefficientRegrouping.deltaCodeIso
      A (single 1) B (single 1) D).hom)
      (eqToHom e' ≫ (JTCoarseRegroupingAssembly.correctedRegroup T a c hac).hom) := by
  subst A
  subst B
  subst D
  exact heq_of_eq (native_view T a c hac N e)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev pre (W : Source) {S T : SSet.{0}} (f : S ⟶ T) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map f) W

private theorem pre_comp (W : Source) {S T U : SSet.{0}} (f : S ⟶ T) (g : T ⟶ U) :
    pre W (f ≫ g) = pre W g ≫ pre W f := by
  unfold pre
  rw [ReversalDiscreteFreeColimits.discreteFree.map_comp]
  exact diagramMappingPrecomp_comp _ _ W

private theorem coefficient_transport (W : Source) {N C G : NecklaceCode}
    {k : SimplexCategory} (e : N = C) (f : C ⟶ G)
    (a : SSet.stdSimplex.obj k ⟶ TripleBeadEndpointLabel.labels W C)
    (b : SSet.stdSimplex.obj k ⟶ TripleBeadEndpointLabel.labels W G)
    (d : SSet.stdSimplex.obj k ⟶ TripleBeadEndpointLabel.labels W N)
    (ha : a = b ≫ pre W f.map) (hd : a ≫ pre W (eqToHom e).map = d) :
    d = b ≫ pre W (eqToHom e ≫ f).map := by
  rw [← hd, ha, Category.assoc, ← pre_comp]
  rfl

private theorem same_map_coefficient (W : Source) {N G : NecklaceCode}
    {k : SimplexCategory} (f g : N ⟶ G) (h : f = g)
    (b : SSet.stdSimplex.obj k ⟶ TripleBeadEndpointLabel.labels W G)
    (d : SSet.stdSimplex.obj k ⟶ TripleBeadEndpointLabel.labels W N)
    (hd : d = b ≫ pre W f.map) : d = b ≫ pre W g.map := by
  rw [← h]
  exact hd

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The original shared insertion choice index. -/
abbrev Index := JTSharedInsertionChoices.Index F j

private abbrev E := single 1
private abbrev Acode (p : Index F j) := JTSharedInsertionCoarseRawData.leftCode F j p
private abbrev Bcode (p : Index F j) := JTSharedInsertionCoarseRawData.intervalCode F j p
private abbrev Dcode (p : Index F j) := JTSharedInsertionCoarseRawData.rightCode F j p
private abbrev native (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes (JTSharedInsertionCoarseLabels.labels F j)).obj p

/-- The same entire grouped code, written using the actual five coefficient pieces. -/
abbrev groupedCode (p : Index F j) :=
  JTCoarseCoefficientRegrouping.groupedCode (Acode F j p) E (Bcode F j p) E (Dcode F j p)

/-- The exact canonical native regrouping used by complete coefficient preservation. -/
def regroup (p : Index F j) : native F j p ⟶ groupedCode F j p :=
  eqToHom (JTSharedInsertionCoarseRawData.code_eq F j p) ≫
    (JTCoarseCoefficientRegrouping.deltaCodeIso
      (Acode F j p) E (Bcode F j p) E (Dcode F j p)).hom

private abbrev pairs := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j
private abbrev T (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes L).obj ((pairs F j).obj p).1
private abbrev a (p : Index F j) := ((pairs F j).obj p).2.left.val
private abbrev c (p : Index F j) := ((pairs F j).obj p).2.right.val
private abbrev hac (p : Index F j) := ((pairs F j).obj p).2.le

private theorem left_code (p : Index F j) :
    Acode F j p = wedge (intervalOver.{0} (T F j p) 0 (a F j p) (Fin.zero_le _)).code E := rfl

private theorem middle_code (p : Index F j) :
    Bcode F j p = (intervalOver.{0} (T F j p) (a F j p) (c F j p) (hac F j p)).code := rfl

private theorem right_code (p : Index F j) :
    Dcode F j p = wedge E (intervalOver.{0} (T F j p) (c F j p)
      (Fin.last (T F j p).len) (Fin.le_last _)).code := rfl

private theorem native_code (p : Index F j) : native F j p =
    (JTCorrectedCoarseIntervalComparison.coarseOver
      (T F j p) (a F j p) (c F j p) (hac F j p)).code :=
  congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_projection F j p)

private theorem native_heq (p : Index F j) :
    HEq (regroup F j p) (JTSharedInsertionCoarseRegroupedNative.regroup F j p) :=
  native_transport (T F j p) (a F j p) (c F j p) (hac F j p)
    (Acode F j p) (Bcode F j p) (Dcode F j p) (native F j p)
    (left_code F j p) (middle_code F j p) (right_code F j p)
    (JTSharedInsertionCoarseRawData.code_eq F j p) (native_code F j p)

set_option maxHeartbeats 400000 in
/-- Its code view is the SAME native regrouping whose original assembly square is checked. -/
theorem regroup_native (p : Index F j) :
    regroup F j p = JTSharedInsertionCoarseRegroupedNative.regroup F j p :=
  eq_of_heq (native_heq F j p)

private def transportedCoefficient (p : Index F j) :=
  coefficient_transport W (JTSharedInsertionCoarseRawData.code_eq F j p)
    (JTCoarseCoefficientRegrouping.deltaCodeIso
      (Acode F j p) E (Bcode F j p) E (Dcode F j p)).hom
    (JTCoarseCoefficientRegrouping.sourceCoefficient (JTSharedInsertionCoarseRawData.data F j p))
    (JTCoarseCoefficientRegrouping.groupedCoefficient (JTSharedInsertionCoarseRawData.data F j p))
    (JTSharedInsertionCoarseRawData.orderedCoefficient F j p)
    (JTCoarseCoefficientRegrouping.coefficient (JTSharedInsertionCoarseRawData.data F j p))
    (JTSharedInsertionCoarseRawData.source_ordered F j p)

private def wholeProof (p : Index F j) :=
  same_map_coefficient W (regroup F j p) (JTSharedInsertionCoarseRegroupedNative.regroup F j p)
    (regroup_native F j p)
    (JTCoarseCoefficientRegrouping.groupedCoefficient (JTSharedInsertionCoarseRawData.data F j p))
    (JTSharedInsertionCoarseRawData.orderedCoefficient F j p) (transportedCoefficient F j p)

/-- The whole ACTUAL ordered coefficient is preserved, with arbitrary varying joint rows. -/
theorem coefficient (p : Index F j) :
    JTSharedInsertionCoarseRawData.orderedCoefficient F j p =
      JTCoarseCoefficientRegrouping.groupedCoefficient
          (JTSharedInsertionCoarseRawData.data F j p) ≫
        pre W (JTSharedInsertionCoarseRegroupedNative.regroup F j p).map :=
  wholeProof F j p

end
end DaggerModels.PartII.JTSharedInsertionCoarseRegroupedCoefficient
