import DaggerModelsPartII.JTSharedInsertionCoarseLabels
import DaggerModelsPartII.JTSharedInsertionSeamSurroundings

/-!
# Coalesce only the inserted cut to the given chart's right endpoint

The chart, original source, entire all-vertex tuple, higher-choice clock and
full chain are retained. Both outside choices and all four edges agree exactly.
This is an endofunctor, not a natural arrow from an arbitrary b to c over the
identity chart. No weakness, raw equation or evaluation comparison is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseCoalescence

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)
open GrothendieckTotalElements (totalDiagram)

noncomputable section

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

private def coverMap {B : Type} [SmallCategory B] (G : B ⥤ B) (X : Bᵒᵖ ⥤ SSet.{0})
    (σ : X ⟶ G.op ⋙ X) : (totalDiagram X).Elementsᵒᵖ ⥤ (totalDiagram X).Elementsᵒᵖ :=
  (((Functor.uncurry.map σ).mapElements) ⋙ reindex G.op X).op

private theorem reindex_ordinals {B C : Type} [SmallCategory B] [SmallCategory C]
    (G : B ⥤ C) (K N : C ⥤ SimplexCategory) :
    JTJointPairChainDiagram.reindex G K N ⋙ TimePrismChainDiagram.ordinals K N =
      TimePrismChainDiagram.ordinals (G ⋙ K) (G ⋙ N) := rfl

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- Insert the GIVEN chart's last cut, without choosing a new chart or brackets. -/
def lastSection : JTJointSubdivisionBeadCharts.Index F j ⥤
    JTJointSubdivisionInsertion.Index F j where
  obj p := ⟨p, ⟨p.2.lastCut, p.2.adjacent.2.2.1, le_rfl⟩⟩
  map f := ⟨f, Subtype.ext
    (JTJointPairSourceDiagram.right_map F j ((JTJointSubdivisionBeadCharts.toPairs F j).map f))⟩
  map_id p := by apply CategoryOfElements.ext; rfl
  map_comp f g := by apply CategoryOfElements.ext; rfl

/-- Replace only the proposed inserted cut by the same chart's right endpoint. -/
abbrev rhoInsertion : JTJointSubdivisionInsertion.Index F j ⥤
    JTJointSubdivisionInsertion.Index F j :=
  JTJointSubdivisionInsertion.toCharts F j ⋙ lastSection F j

/-- The entire given chart and every actual chart arrow are unchanged. -/
theorem rhoInsertion_toCharts :
    rhoInsertion F j ⋙ JTJointSubdivisionInsertion.toCharts F j =
      JTJointSubdivisionInsertion.toCharts F j := rfl

/-- The original source object and arrow remain literal. -/
theorem rhoInsertion_base : rhoInsertion F j ⋙ JTJointSubdivisionInsertion.base F j =
    JTJointSubdivisionInsertion.base F j := rfl

/-- The original all-vertex tuple is the IDENTITY tuple in every full degree. -/
def tupleMap : JTSharedInsertionChoices.spaces F j ⟶
    (rhoInsertion F j).op ⋙ JTSharedInsertionChoices.spaces F j := 𝟙 _

/-- Retain the SAME whole tuple and higher simplex degree over the coalesced insertion. -/
def rhoCover : JTSharedInsertionChoices.Cover F j ⥤ JTSharedInsertionChoices.Cover F j :=
  coverMap (rhoInsertion F j) (JTSharedInsertionChoices.spaces F j) (tupleMap F j)

/-- Only the middle insertion coordinate changes under the whole tuple cover. -/
theorem rhoCover_projection :
    rhoCover F j ⋙ JTSharedInsertionChoices.projection F j =
      JTSharedInsertionChoices.projection F j ⋙ rhoInsertion F j := rfl

/-- The full original coefficient functor is unchanged. -/
theorem rhoCover_coefficient :
    rhoCover F j ⋙ JTSharedInsertionChoices.coefficient F j =
      JTSharedInsertionChoices.coefficient F j := rfl

/-- The complete original higher-choice clock is unchanged. -/
theorem rhoCover_clock : rhoCover F j ⋙ JTSharedInsertionChoices.clock F j =
    JTSharedInsertionChoices.clock F j := rfl

/-- Coalesce the middle while retaining the literal common full chain. -/
def rhoIndex : JTSharedInsertionChoices.Index F j ⥤ JTSharedInsertionChoices.Index F j :=
  JTJointPairChainDiagram.reindex (rhoCover F j)
    (JTSharedInsertionChoices.coefficient F j) (JTSharedInsertionChoices.clock F j)

/-- The underlying whole tuple cover map is exactly rhoCover. -/
theorem rhoIndex_base : rhoIndex F j ⋙ JTSharedInsertionChoices.base F j =
    JTSharedInsertionChoices.base F j ⋙ rhoCover F j := rfl

/-- No original source object or arrow changes. -/
theorem rhoIndex_original : rhoIndex F j ⋙ JTSharedInsertionChainSupport.originalBase F j =
    JTSharedInsertionChainSupport.originalBase F j := rfl

/-- Every actual chain ordinal and every ordinal operator is identical. -/
theorem rhoIndex_ordinals : rhoIndex F j ⋙ JTSharedInsertionChoices.ordinals F j =
    JTSharedInsertionChoices.ordinals F j :=
  reindex_ordinals (rhoCover F j)
    (JTSharedInsertionChoices.coefficient F j) (JTSharedInsertionChoices.clock F j)

/-- The coefficient projection is unchanged on the entire literal full chain. -/
theorem rhoIndex_toOriginal (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionChoices.toOriginal F j).app ((rhoIndex F j).obj p) =
      (JTSharedInsertionChoices.toOriginal F j).app p := rfl

/-- The common higher-choice time projection is unchanged as well. -/
theorem rhoIndex_toTime (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionChoices.toTime F j).app ((rhoIndex F j).obj p) =
      (JTSharedInsertionChoices.toTime F j).app p := rfl

/-- The earlier actual mark remains the same under all operators. -/
theorem rhoIndex_earlier : rhoIndex F j ⋙ JTSharedInsertionChainSupport.marks F j 0 =
    JTSharedInsertionChainSupport.marks F j 0 := rfl

/-- The middle actual mark becomes exactly the given later mark. -/
theorem rhoIndex_middle : rhoIndex F j ⋙ JTSharedInsertionChainSupport.marks F j 1 =
    JTSharedInsertionChainSupport.marks F j 2 := rfl

/-- The later actual mark remains unchanged. -/
theorem rhoIndex_later : rhoIndex F j ⋙ JTSharedInsertionChainSupport.marks F j 2 =
    JTSharedInsertionChainSupport.marks F j 2 := rfl

/-- The earlier full higher-choice object is the original tuple coordinate. -/
theorem earlier_obj (p : JTSharedInsertionChoices.Cover F j) :
    (JTSharedInsertionChoices.earlier F j).obj ((rhoCover F j).obj p) =
      (JTSharedInsertionChoices.earlier F j).obj p := rfl

/-- The later higher choice also retains its original tuple coordinate. -/
theorem later_obj (p : JTSharedInsertionChoices.Cover F j) :
    (JTSharedInsertionChoices.later F j).obj ((rhoCover F j).obj p) =
      (JTSharedInsertionChoices.later F j).obj p := rfl

/-- The earlier entire coefficient-time chain is unchanged. -/
theorem earlier_chain_obj (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionChoices.earlierChain F j).obj ((rhoIndex F j).obj p) =
      (JTSharedInsertionChoices.earlierChain F j).obj p := rfl

/-- The later entire coefficient-time chain is unchanged. -/
theorem later_chain_obj (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionChoices.laterChain F j).obj ((rhoIndex F j).obj p) =
      (JTSharedInsertionChoices.laterChain F j).obj p := rfl

/-- Ending at a uses the exact original shared edge. -/
theorem earlier_ending (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionIncidentEdges.ending F j 0).app ((rhoIndex F j).obj p) =
      (JTSharedInsertionIncidentEdges.ending F j 0).app p := rfl

/-- Starting at a uses the exact original shared edge. -/
theorem earlier_starting (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionIncidentEdges.starting F j 0).app ((rhoIndex F j).obj p) =
      (JTSharedInsertionIncidentEdges.starting F j 0).app p := rfl

/-- Ending at c uses the exact original shared edge. -/
theorem later_ending (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionIncidentEdges.ending F j 2).app ((rhoIndex F j).obj p) =
      (JTSharedInsertionIncidentEdges.ending F j 2).app p := rfl

/-- Starting at c uses the exact original shared edge. -/
theorem later_starting (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionIncidentEdges.starting F j 2).app ((rhoIndex F j).obj p) =
      (JTSharedInsertionIncidentEdges.starting F j 2).app p := rfl

/-- The outside paired choice and its full common chain are the original ones. -/
theorem coarse_pair_obj (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionCoarseChoice.toPairChain F j).obj ((rhoIndex F j).obj p) =
      (JTSharedInsertionCoarseChoice.toPairChain F j).obj p := rfl

/-- The full corrected prefix coefficient is unchanged. -/
theorem coarse_left (p : JTSharedInsertionChoices.Index F j) :
    ((JTSharedInsertionCoarseLabels.family F j).data ((rhoIndex F j).obj p)).left =
      ((JTSharedInsertionCoarseLabels.family F j).data p).left := rfl

/-- The whole a,c coefficient, with its two corrections, is unchanged. -/
theorem coarse_middle (p : JTSharedInsertionChoices.Index F j) :
    ((JTSharedInsertionCoarseLabels.family F j).data ((rhoIndex F j).obj p)).middle =
      ((JTSharedInsertionCoarseLabels.family F j).data p).middle := rfl

/-- The full corrected suffix coefficient is unchanged. -/
theorem coarse_right (p : JTSharedInsertionChoices.Index F j) :
    ((JTSharedInsertionCoarseLabels.family F j).data ((rhoIndex F j).obj p)).right =
      ((JTSharedInsertionCoarseLabels.family F j).data p).right := rfl

/-- The lower pair at coalescence is the entire original outside pair a,c. -/
theorem lower_pair (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionSeamSurroundings.lowerPairs F j).obj ((rhoIndex F j).obj p) =
      (JTJointPairGapChainLabels.oldPairs F j).obj
        ((JTSharedInsertionCoarseChoice.toPairChain F j).obj p) := rfl

/-- The upper interval is genuinely diagonal, including zero-length original cases. -/
theorem upper_code_point (p : JTSharedInsertionChoices.Index F j) :
    (JTSharedInsertionSeamSurroundings.upperNative F j).obj ((rhoIndex F j).obj p) = point :=
  intervalCode_diagonal _ _

end
end DaggerModels.PartII.JTSharedInsertionCoarseCoalescence
