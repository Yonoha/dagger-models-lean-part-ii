import DaggerModelsPartII.JTSharedInsertionChoices
import DaggerModelsPartII.JTJointPairWhiskeredSurroundings

/-!
# The same tuple and full chain at the two outside cuts of an insertion

The original all-vertex tuple supplies both choices of the actual coarse pair.
The higher-choice clock, original coefficient and every full-chain vertex are
retained. No new choices, weak-projection assertion or raw equation is added.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSharedInsertionCoarseChoice

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)
open GrothendieckTotalElements (totalDiagram)

noncomputable section

private def pairAfter {B C : Type} [SmallCategory B] [SmallCategory C]
    (G : B ⥤ C) {X : B ⥤ SSet.{0}} {Y Z : C ⥤ SSet.{0}}
    (l : X ⟶ G ⋙ Y) (r : X ⟶ G ⋙ Z) :
    X ⟶ G ⋙ (Functor.diag C ⋙ Y.prod Z ⋙ MonoidalCategory.tensor SSet.{0}) where
  app b := lift (l.app b) (r.app b)
  naturality {a b} f := by
    change X.map f ≫ lift (l.app b) (r.app b) =
      lift (l.app a) (r.app a) ≫ (Y.map (G.map f) ⊗ₘ Z.map (G.map f))
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc] using l.naturality f
    · simpa only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc] using r.naturality f

private def reindex {B C : Type} [SmallCategory B] [SmallCategory C]
    (G : B ⥤ C) (X : C ⥤ SSet.{0}) :
    (totalDiagram (G ⋙ X)).Elements ⥤ (totalDiagram X).Elements where
  obj p := ⟨(G.obj p.1.1, p.1.2), p.2⟩
  map f := ⟨(G.map f.val.1, f.val.2), f.property⟩
  map_id p := by
    apply CategoryOfElements.ext
    exact Prod.ext (G.map_id p.1.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext (G.map_comp f.val.1 g.val.1) rfl

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The actual outside cut pair of the given coarse chart, including equal cuts. -/
abbrev pairBase : JTJointSubdivisionInsertion.Index F j ⥤ JTJointPairSourceDiagram.Index F j :=
  JTJointSubdivisionInsertion.toCharts F j ⋙ JTJointSubdivisionBeadCharts.toPairs F j

/-- Pair the two evaluations of the SAME full original tuple, without choosing edges. -/
def lookup : JTSharedInsertionChoices.spaces F j ⟶
    (pairBase F j).op ⋙ JTJointPairChoiceCover.spaces F j :=
  pairAfter (pairBase F j).op
    (Y := (JTJointPairSourceDiagram.leftCut F j).op ⋙ JTActualJointChoiceCover.spaces F j)
    (Z := (JTJointPairSourceDiagram.rightCut F j).op ⋙ JTActualJointChoiceCover.spaces F j)
    (JTSharedInsertionChoices.earlierLookup F j) (JTSharedInsertionChoices.laterLookup F j)

/-- The full higher paired choice keeps exactly the original common tuple degree. -/
def toPairCover : JTSharedInsertionChoices.Cover F j ⥤ JTJointPairChoiceCover.Cover F j :=
  (((Functor.uncurry.map (lookup F j)).mapElements) ⋙
    reindex (pairBase F j).op (JTJointPairChoiceCover.spaces F j)).op

/-- Retain the actual outside cuts and their complete original source arrows. -/
theorem toPairCover_projection :
    toPairCover F j ⋙ JTJointPairChoiceCover.projection F j =
      JTSharedInsertionChoices.projection F j ⋙ pairBase F j := rfl

/-- The original coefficient is unchanged by pairing the outside choices. -/
theorem toPairCover_coefficient :
    toPairCover F j ⋙ JTJointPairChainDiagram.coefficient F j =
      JTSharedInsertionChoices.coefficient F j := rfl

/-- Both paired higher choices use the original tuple's entire simplex clock. -/
theorem toPairCover_clock :
    toPairCover F j ⋙ JTJointPairChainDiagram.clock F j =
      JTSharedInsertionChoices.clock F j := rfl

/-- The paired earlier object is the exact earlier lookup of the original tuple. -/
theorem earlier_obj (p : JTSharedInsertionChoices.Cover F j) :
    (JTJointPairChoiceCover.earlier F j).obj ((toPairCover F j).obj p) =
      (JTSharedInsertionChoices.earlier F j).obj p := rfl

/-- The paired later object is the exact later lookup of that same tuple. -/
theorem later_obj (p : JTSharedInsertionChoices.Cover F j) :
    (JTJointPairChoiceCover.later F j).obj ((toPairCover F j).obj p) =
      (JTSharedInsertionChoices.later F j).obj p := rfl

/-- Keep the very same common full chain while passing to the outside pair. -/
def toPairChain : JTSharedInsertionChoices.Index F j ⥤ JTJointPairChainDiagram.Index F j :=
  JTJointPairChainDiagram.reindex (toPairCover F j)
    (JTJointPairChainDiagram.coefficient F j) (JTJointPairChainDiagram.clock F j)

/-- Forgetting the chain retains precisely the paired tuple constructed above. -/
theorem toPairChain_base :
    toPairChain F j ⋙ JTJointPairChainDiagram.base F j =
      JTSharedInsertionChoices.base F j ⋙ toPairCover F j := rfl

/-- Every common full-chain ordinal and every operator is unchanged. -/
theorem toPairChain_ordinals :
    toPairChain F j ⋙ JTJointPairChainDiagram.ordinals F j =
      JTSharedInsertionChoices.ordinals F j := rfl

/-- The paired chain keeps its exact original coefficient projection. -/
theorem toPairChain_toOriginal (p : JTSharedInsertionChoices.Index F j) :
    (JTJointPairChainDiagram.toOriginal F j).app ((toPairChain F j).obj p) =
      (JTSharedInsertionChoices.toOriginal F j).app p := rfl

/-- The paired chain keeps its exact projection to the common tuple clock. -/
theorem toPairChain_toTime (p : JTSharedInsertionChoices.Index F j) :
    (JTJointPairChainDiagram.toTime F j).app ((toPairChain F j).obj p) =
      (JTSharedInsertionChoices.toTime F j).app p := rfl

/-- The coarse pair's ending edge at a is literally the shared earlier ending edge. -/
theorem earlier_ending (p : JTSharedInsertionChoices.Index F j) :
    (JTActualJointChoiceChainGraph.chainEnding F j).app
        ((JTJointPairChainDiagram.earlier F j).obj ((toPairChain F j).obj p)) =
      (JTActualJointChoiceChainGraph.chainEnding F j).app
        ((JTSharedInsertionChoices.earlierChain F j).obj p) := rfl

/-- The coarse pair's starting edge at a is the same shared earlier starting edge. -/
theorem earlier_starting (p : JTSharedInsertionChoices.Index F j) :
    (JTActualJointChoiceChainGraph.chainStarting F j).app
        ((JTJointPairChainDiagram.earlier F j).obj ((toPairChain F j).obj p)) =
      (JTActualJointChoiceChainGraph.chainStarting F j).app
        ((JTSharedInsertionChoices.earlierChain F j).obj p) := rfl

/-- The coarse pair's ending edge at c is the same shared later ending edge. -/
theorem later_ending (p : JTSharedInsertionChoices.Index F j) :
    (JTActualJointChoiceChainGraph.chainEnding F j).app
        ((JTJointPairChainDiagram.later F j).obj ((toPairChain F j).obj p)) =
      (JTActualJointChoiceChainGraph.chainEnding F j).app
        ((JTSharedInsertionChoices.laterChain F j).obj p) := rfl

/-- The coarse pair's starting edge at c is the same shared later starting edge. -/
theorem later_starting (p : JTSharedInsertionChoices.Index F j) :
    (JTActualJointChoiceChainGraph.chainStarting F j).app
        ((JTJointPairChainDiagram.later F j).obj ((toPairChain F j).obj p)) =
      (JTActualJointChoiceChainGraph.chainStarting F j).app
        ((JTSharedInsertionChoices.laterChain F j).obj p) := rfl

end
end DaggerModels.PartII.JTSharedInsertionCoarseChoice
