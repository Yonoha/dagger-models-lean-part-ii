import DaggerModelsPartII.JTIncidentBeadChoiceDiagram
import DaggerModelsPartII.JTAllVertexChoiceProduct

/-!
# Simultaneous actual incident choices at every original vertex over a joint

This instantiates the finite all-vertex product with the actual incident-union
relative edge spaces. Every original operator, including vertex coalescences,
acts on the complete tuple. The resulting full choice cover is weak over the
ORIGINAL source category, with a common higher simplicial choice degree.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTIncidentAllVertexChoices

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open DaggerOriginalProductGadget (pointMap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

/-- Actual incident-union relative choices simultaneously at every original vertex above j. -/
abbrev spaces : Aᵒᵖ ⥤ SSet.{0} :=
  JTAllVertexChoiceProduct.tuple F j (JTIncidentBeadChoiceDiagram.spaces F j)

/-- Every higher simplex is literally a full tuple of the actual incident choices. -/
theorem spaces_obj (a : A) (n : SimplexCategoryᵒᵖ) :
    ((spaces F j).obj (op a)).obj n =
      (∀ v : (JTExactlyMarkedSourceDiagram.vertices F j).obj a,
        ((JTIncidentBeadChoiceDiagram.spaces F j).obj (op ⟨a, v⟩)).obj n) := rfl

/-- Lookup at an exactly marked vertex is natural for every original source operator. -/
abbrev evaluation : (JTExactlyMarkedSourceDiagram.base F j).op ⋙ spaces F j ⟶
    JTIncidentBeadChoiceDiagram.spaces F j :=
  JTAllVertexChoiceProduct.evaluation F j (JTIncidentBeadChoiceDiagram.spaces F j)

/-- Lookup retains the complete common higher simplex degree. -/
theorem evaluation_app (p : JTExactlyMarkedSourceDiagram.Index F j)
    (n : SimplexCategoryᵒᵖ) (q : ((spaces F j).obj (op p.1)).obj n) :
    ((evaluation F j).app (op p)).app n q = q p.2 := rfl

/-- The actual all-vertex tuple is weakly contractible under original injective fibrancy. -/
theorem spaces_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) (a : Aᵒᵖ) :
    GW (pointMap ((spaces F j).obj a)) :=
  JTAllVertexChoiceProduct.tuple_point_GW F j (JTIncidentBeadChoiceDiagram.spaces F j)
    (JTIncidentBeadChoiceDiagram.spaces_point_GW F j hW) a

/-- The full actual all-vertex choice cover, with one common higher simplex clock. -/
abbrev Cover := JTAllVertexChoiceProduct.Cover F j (JTIncidentBeadChoiceDiagram.spaces F j)

/-- Forget all choices and their common degree, retaining the full original source. -/
abbrev projection : Cover F j ⥤ A :=
  JTAllVertexChoiceProduct.projection F j (JTIncidentBeadChoiceDiagram.spaces F j)

/-- The actual all-vertex incident-choice cover is weak over the ORIGINAL category A. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j)) :=
  JTAllVertexChoiceProduct.projection_weak F j (JTIncidentBeadChoiceDiagram.spaces F j)
    (JTIncidentBeadChoiceDiagram.spaces_point_GW F j hW)

/-- A full actual tuple together with a named original vertex, at the same choice degree. -/
abbrev MarkedCover :=
  JTAllVertexChoiceProduct.MarkedCover F j (JTIncidentBeadChoiceDiagram.spaces F j)

/-- Forget the named vertex while preserving the tuple, original arrow and common degree. -/
abbrev toTuple : MarkedCover F j ⥤ Cover F j :=
  JTAllVertexChoiceProduct.toTuple F j (JTIncidentBeadChoiceDiagram.spaces F j)

/-- Evaluate the actual tuple in the full incident-choice cover at its named vertex. -/
abbrev toChoice : MarkedCover F j ⥤ JTIncidentBeadChoiceDiagram.Cover F j :=
  JTAllVertexChoiceProduct.toChoice F j (JTIncidentBeadChoiceDiagram.spaces F j)

/-- Lookup and forgetting agree on the exact original source object and arrow. -/
theorem toChoice_source :
    toChoice F j ⋙ JTIncidentBeadChoiceDiagram.projection F j ⋙
        JTExactlyMarkedSourceDiagram.base F j =
      toTuple F j ⋙ projection F j := rfl

/-- Lookup retains every common higher simplicial choice operator. -/
theorem toChoice_time :
    toChoice F j ⋙ SynchronizedSimplicialParameters.time
        (JTIncidentBeadChoiceDiagram.spaces F j) =
      toTuple F j ⋙ SynchronizedSimplicialParameters.time (spaces F j) := rfl

/-- Lookup followed by restriction gives the original actual vertex-supported choices. -/
abbrev toActual : MarkedCover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  toChoice F j ⋙ JTIncidentBeadChoiceDiagram.toActual F j

/-- Lookup and restriction retain the original source object and every original arrow. -/
theorem toActual_source :
    toActual F j ⋙ JTActualJointChoiceCover.projection F j ⋙
        JTExactlyMarkedSourceDiagram.base F j =
      toTuple F j ⋙ projection F j := rfl

/-- Lookup and restriction retain the full common higher simplicial choice clock. -/
theorem toActual_time :
    toActual F j ⋙ SynchronizedSimplicialParameters.time (JTActualJointChoiceCover.spaces F j) =
      toTuple F j ⋙ SynchronizedSimplicialParameters.time (spaces F j) := rfl

end
end DaggerModels.PartII.JTIncidentAllVertexChoices
