import DaggerModelsPartII.JTJointPairChoiceCover
import DaggerModelsPartII.JTActualJointChoiceChainGraph

/-! One full coefficient-time chain for both ordered cut choices. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointPairChainDiagram

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- Reindex full coefficient-time chains along a base functor. -/
def reindex {B I : Type} [SmallCategory B] [SmallCategory I]
    (G : B ⥤ I) (K N : I ⥤ SimplexCategory) :
    TimePrismChainDiagram.Index (G ⋙ K) (G ⋙ N) ⥤
      TimePrismChainDiagram.Index K N where
  obj p := ⟨G.obj p.base, p.chain⟩
  map f := ⟨G.map f.base, f.mapsTo⟩
  map_id p := TimePrismChainDiagram.hom_ext K N (G.map_id p.base)
  map_comp f g := TimePrismChainDiagram.hom_ext K N (G.map_comp f.base g.base)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

/-- The unchanged original coefficient on simultaneous higher choices. -/
abbrev coefficient : JTJointPairChoiceCover.Cover F j ⥤ SimplexCategory :=
  JTJointPairChoiceCover.projection F j ⋙ JTJointPairSourceDiagram.base F j ⋙
    JTJointRelativeGraphFamily.coefficient (L := L)

/-- The one simplex clock shared by both higher choices. -/
abbrev clock : JTJointPairChoiceCover.Cover F j ⥤ SimplexCategory :=
  SynchronizedSimplicialParameters.time (JTJointPairChoiceCover.spaces F j)

/-- Full chains through the common original coefficient and common clock. -/
abbrev Index := TimePrismChainDiagram.Index (coefficient F j) (clock F j)

/-- Forget a full chain while retaining both relative edge choices. -/
abbrev base : Index F j ⥤ JTJointPairChoiceCover.Cover F j :=
  TimePrismChainDiagram.base _ _

/-- The ordinal of each common full chain. -/
abbrev ordinals : Index F j ⥤ SimplexCategory :=
  TimePrismChainDiagram.ordinals _ _

/-- Each common chain covers the unchanged original coefficient degree. -/
abbrev toOriginal : ordinals F j ⟶ base F j ⋙ coefficient F j :=
  TimePrismChainDiagram.coeffProjection _ _

/-- The same chain also projects to the one shared higher-choice clock. -/
abbrev toTime : ordinals F j ⟶ base F j ⋙ clock F j :=
  TimePrismChainDiagram.timeProjection _ _

theorem toOriginal_surjective (p : Index F j) :
    Function.Surjective ((toOriginal F j).app p).toOrderHom :=
  TimePrismChainDiagram.coeffProjection_surjective _ _ p

theorem base_weak : WeakEquivalence (nerveMap (base F j)) :=
  TimePrismChainProjection.projection_weak _ _

/-- The earlier choice, viewed with precisely the same full chain. -/
def earlier : Index F j ⥤ JTActualJointChoiceChainGraph.Index F j :=
  reindex (JTJointPairChoiceCover.earlier F j)
    (JTActualJointChoicePrism.coefficient F j)
    (JTActualJointChoicePrism.choiceTime F j)

/-- The later choice, viewed with precisely the same full chain. -/
def later : Index F j ⥤ JTActualJointChoiceChainGraph.Index F j :=
  reindex (JTJointPairChoiceCover.later F j)
    (JTActualJointChoicePrism.coefficient F j)
    (JTActualJointChoicePrism.choiceTime F j)


/-- Both cut choices retain their exact base objects and arrows. -/
theorem earlier_base :
    earlier F j ⋙ JTActualJointChoiceChainGraph.base F j =
      base F j ⋙ JTJointPairChoiceCover.earlier F j := rfl

theorem later_base :
    later F j ⋙ JTActualJointChoiceChainGraph.base F j =
      base F j ⋙ JTJointPairChoiceCover.later F j := rfl

/-- The two cuts have one literal original source family. -/
theorem earlier_original_base :
    earlier F j ⋙ JTActualJointChoiceChainGraph.base F j ⋙
        JTActualJointChoiceCover.projection F j ⋙ JTExactlyMarkedSourceDiagram.base F j =
      base F j ⋙ JTJointPairChoiceCover.projection F j ⋙
        JTJointPairSourceDiagram.base F j := rfl

theorem later_original_base :
    later F j ⋙ JTActualJointChoiceChainGraph.base F j ⋙
        JTActualJointChoiceCover.projection F j ⋙ JTExactlyMarkedSourceDiagram.base F j =
      base F j ⋙ JTJointPairChoiceCover.projection F j ⋙
        JTJointPairSourceDiagram.base F j := rfl

/-- Neither cut reorders or replaces any vertex of a common full chain. -/
theorem earlier_ordinals :
    earlier F j ⋙ JTActualJointChoiceChainGraph.ordinals F j = ordinals F j := rfl

theorem later_ordinals :
    later F j ⋙ JTActualJointChoiceChainGraph.ordinals F j = ordinals F j := rfl

/-- The original coefficient functor is literally the same at both cuts. -/
theorem earlier_coefficient :
    JTJointPairChoiceCover.earlier F j ⋙ JTActualJointChoicePrism.coefficient F j =
      coefficient F j := rfl

theorem later_coefficient :
    JTJointPairChoiceCover.later F j ⋙ JTActualJointChoicePrism.coefficient F j =
      coefficient F j := rfl

/-- The complete higher-choice clock is literally shared at both cuts. -/
theorem earlier_clock :
    JTJointPairChoiceCover.earlier F j ⋙ JTActualJointChoicePrism.choiceTime F j =
      clock F j := rfl

theorem later_clock :
    JTJointPairChoiceCover.later F j ⋙ JTActualJointChoicePrism.choiceTime F j =
      clock F j := rfl

/-- Both coefficient projections are the same map of ordinals on every chain. -/
theorem earlier_toOriginal (p : Index F j) :
    (JTActualJointChoiceChainGraph.toOriginal F j).app ((earlier F j).obj p) =
      (toOriginal F j).app p := rfl

theorem later_toOriginal (p : Index F j) :
    (JTActualJointChoiceChainGraph.toOriginal F j).app ((later F j).obj p) =
      (toOriginal F j).app p := rfl

/-- Both time projections are the same map of ordinals on every chain. -/
theorem earlier_toTime (p : Index F j) :
    (JTActualJointChoiceChainGraph.toTime F j).app ((earlier F j).obj p) =
      (toTime F j).app p := rfl

theorem later_toTime (p : Index F j) :
    (JTActualJointChoiceChainGraph.toTime F j).app ((later F j).obj p) =
      (toTime F j).app p := rfl


end
end DaggerModels.PartII.JTJointPairChainDiagram

