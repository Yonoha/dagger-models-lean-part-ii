import DaggerModelsPartII.JTCoarseRegroupingAssembly
import DaggerModelsPartII.JTSharedInsertionCoarseNative

/-!
# Regroup the ACTUAL coarse native assembly before the original target Q

The existing canonical coarse assembly and five-piece regrouping are applied to
actual F,j,p. All original intervals and all four correction pieces are retained.
The complete native assembly square is proved before postcomposition into Q.
No coefficient, raw, evaluation or source-weakness premise is added.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseRegroupedNative

noncomputable section

private def groupedAssemblyCode (T : NecklaceCode) (a c : Fin (T.len + 1))
    (hac : a ≤ c) : (JTCoarseRegroupingAssembly.correctedGrouped T a c hac).code ⟶ T where
  map := (JTCoarseRegroupingAssembly.correctedGrouped T a c hac).map
  first := (JTCoarseRegroupingAssembly.correctedGrouped T a c hac).first
  last := (JTCoarseRegroupingAssembly.correctedGrouped T a c hac).last

private theorem native_square (T : NecklaceCode) (a c : Fin (T.len + 1))
    (hac : a ≤ c) :
    (JTCoarseRegroupingAssembly.correctedRegroup T a c hac).hom ≫
        groupedAssemblyCode T a c hac = JTCorrectedCoarseIntervalComparison.assembly T a c hac :=
  NecklaceCode.Hom.ext (JTCoarseRegroupingAssembly.corrected_assembly T a c hac)

private theorem transport_square {N C G T : NecklaceCode} (e : N = C)
    (f : C ⟶ G) (g : G ⟶ T) (n : C ⟶ T) (h : f ≫ g = n) :
    (eqToHom e ≫ f) ≫ g = eqToHom e ≫ n := by
  rw [Category.assoc, h]

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The unchanged shared insertion choices, without triangle-filler choices. -/
abbrev Index := JTSharedInsertionChoices.Index F j

private abbrev pairs := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j
private abbrev T (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes L).obj ((pairs F j).obj p).1
private abbrev a (p : Index F j) := ((pairs F j).obj p).2.left.val
private abbrev c (p : Index F j) := ((pairs F j).obj p).2.right.val
private abbrev hac (p : Index F j) := ((pairs F j).obj p).2.le
private abbrev native (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes (JTSharedInsertionCoarseLabels.labels F j)).obj p

private theorem code_eq (p : Index F j) : native F j p =
    (JTCorrectedCoarseIntervalComparison.coarseOver
      (T F j p) (a F j p) (c F j p) (hac F j p)).code :=
  congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_projection F j p)

/-- The exact whole grouped coarse code over the SAME original source object. -/
abbrev groupedCode (p : Index F j) :=
  (JTCoarseRegroupingAssembly.correctedGrouped
    (T F j p) (a F j p) (c F j p) (hac F j p)).code

/-- Regroup the ACTUAL native code using only its proved canonical identification. -/
def regroup (p : Index F j) : native F j p ⟶ groupedCode F j p :=
  eqToHom (code_eq F j p) ≫
    (JTCoarseRegroupingAssembly.correctedRegroup
      (T F j p) (a F j p) (c F j p) (hac F j p)).hom

/-- The complete grouped assembly into the unchanged original necklace, before Q. -/
def groupedAssembly (p : Index F j) : groupedCode F j p ⟶
    (JTParametrizedTargetFamilies.codes L).obj
      ((JTSharedInsertionCoarseNative.original F j).obj p) :=
  groupedAssemblyCode (T F j p) (a F j p) (c F j p) (hac F j p)

/-- The full ACTUAL assembly square is an ordinary strict native equality. -/
theorem regroup_assembly (p : Index F j) :
    regroup F j p ≫ groupedAssembly F j p =
      (JTSharedInsertionCoarseNative.assembly F j).app p := by
  rw [JTSharedInsertionCoarseNative.assembly_app]
  exact transport_square (code_eq F j p) _ _ _
    (native_square (T F j p) (a F j p) (c F j p) (hac F j p))

/-- The same complete square on simplicial-set maps, still before original Q. -/
theorem regroup_assembly_map (p : Index F j) :
    (regroup F j p).map ≫ (groupedAssembly F j p).map =
      ((JTSharedInsertionCoarseNative.assembly F j).app p).map :=
  congrArg NecklaceCode.Hom.map (regroup_assembly F j p)

end
end DaggerModels.PartII.JTSharedInsertionCoarseRegroupedNative
