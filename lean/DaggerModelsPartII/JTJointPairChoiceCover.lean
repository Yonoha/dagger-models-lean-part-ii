import DaggerModelsPartII.JTJointPairSourceDiagram
import DaggerModelsPartII.JTActualJointChoiceCover

/-! Simultaneous full endpoint choices for an ordered pair of actual source cuts. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointPairChoiceCover

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTJointPairSourceDiagram (Index leftCut rightCut)
open JTProjectiveOrderedFiberComparison (row)
open GrothendieckTotalElements (totalDiagram)
open DaggerOriginalProductGadget (pointMap pointMap_tensor_GW)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Ord := SimplexCategoryᵒᵖ

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev leftSpaces := (leftCut F j).op ⋙ JTActualJointChoiceCover.spaces F j
private abbrev rightSpaces := (rightCut F j).op ⋙ JTActualJointChoiceCover.spaces F j

/-- Both endpoint pairs of relative edge choices share every full simplex degree. -/
abbrev spaces : (Index F j)ᵒᵖ ⥤ SSet.{0} :=
  Functor.diag (Index F j)ᵒᵖ ⋙ (leftSpaces F j).prod (rightSpaces F j) ⋙
    MonoidalCategory.tensor SSet.{0}

private def toLeft : spaces F j ⟶ leftSpaces F j where
  app p := fst ((leftSpaces F j).obj p) ((rightSpaces F j).obj p)
  naturality _ _ f := tensorHom_fst ((leftSpaces F j).map f) ((rightSpaces F j).map f)

private def toRight : spaces F j ⟶ rightSpaces F j where
  app p := snd ((leftSpaces F j).obj p) ((rightSpaces F j).obj p)
  naturality _ _ f := tensorHom_snd ((leftSpaces F j).map f) ((rightSpaces F j).map f)

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

/-- Keep all four relative edges and every simplex operator over an ordered pair of cuts. -/
abbrev Cover := (totalDiagram (spaces F j)).Elementsᵒᵖ

/-- Retain the actual ordered cut pair, with its original arrow. -/
abbrev projection : Cover F j ⥤ Index F j :=
  (CategoryOfElements.π (totalDiagram (spaces F j)) ⋙
    CategoryTheory.Prod.fst (Index F j)ᵒᵖ Ord).leftOp

/-- The full choice at the earlier cut, with the common simplex degree unchanged. -/
def earlier : Cover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  (((Functor.uncurry.map (toLeft F j)).mapElements) ⋙
    reindex (leftCut F j).op (JTActualJointChoiceCover.spaces F j)).op

/-- The full choice at the later cut, using the same simplex degree. -/
def later : Cover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  (((Functor.uncurry.map (toRight F j)).mapElements) ⋙
    reindex (rightCut F j).op (JTActualJointChoiceCover.spaces F j)).op

theorem earlier_projection :
    earlier F j ⋙ JTActualJointChoiceCover.projection F j =
      projection F j ⋙ leftCut F j := rfl

theorem later_projection :
    later F j ⋙ JTActualJointChoiceCover.projection F j =
      projection F j ⋙ rightCut F j := rfl

/-- Both ends retain literally the same full higher-choice time functor. -/
theorem earlier_time :
    earlier F j ⋙ SynchronizedSimplicialParameters.time (JTActualJointChoiceCover.spaces F j) =
      SynchronizedSimplicialParameters.time (spaces F j) := rfl

theorem later_time :
    later F j ⋙ SynchronizedSimplicialParameters.time (JTActualJointChoiceCover.spaces F j) =
      SynchronizedSimplicialParameters.time (spaces F j) := rfl

/-- Each fiber of simultaneous full endpoint choices is weakly contractible. -/
theorem spaces_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (Index F j)ᵒᵖ) : GW (pointMap ((spaces F j).obj p)) :=
  pointMap_tensor_GW
    (JTActualJointChoiceCover.spaces_point_GW F j hW ((leftCut F j).op.obj p))
    (JTActualJointChoiceCover.spaces_point_GW F j hW ((rightCut F j).op.obj p))

/-- Adjoining all simultaneous choices is a nerve weak cover of the actual
ordered-pair category; no categorical pullback of weak equivalences is assumed. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j)) := by
  let E := (totalDiagram (spaces F j)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff (projection F j)).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (totalDiagram (spaces F j)) ⋙
      CategoryTheory.Prod.fst (Index F j)ᵒᵖ Ord))
  exact SynchronizedSimplicialParameters.projection_weak (spaces F j)
    (spaces_point_GW F j hW)

end
end DaggerModels.PartII.JTJointPairChoiceCover
