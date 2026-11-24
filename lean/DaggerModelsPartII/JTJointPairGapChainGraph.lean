import DaggerModelsPartII.JTJointPairGapChainParameter
import DaggerModelsPartII.JTPrismChainGraphCover

/-! Lift the entire padded gap graph to the one common higher coefficient chain. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointPairGapChainGraph

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointPairChainDiagram.Index F j
private abbrev α := JTJointPairChainDiagram.toOriginal F j
private abbrev X := JTJointPairGapChainParameter.X F j
private abbrev ψ := JTJointPairGapChainParameter.coarseParameter F j

/-- Keep all compatible full-chain coefficient lifts of the padded gap graph. -/
abbrev graph : I F j ⥤ SSet.{0} := JTPrismChainGraphCover.cover (X F j) (ψ F j) (α F j)

/-- Recover the original padded native and full-time graph. -/
abbrev projection : graph F j ⟶ X F j :=
  JTPrismChainGraphCover.projection (X F j) (ψ F j) (α F j)

/-- The lifted parameter has the common pair-chain ordinal at every object. -/
abbrev parameter : graph F j ⟶ JTJointPairChainDiagram.ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter (X F j) (ψ F j) (α F j)

/-- The lifted parameter projects to the exact old-degree padded parameter. -/
theorem parameter_projection :
    parameter F j ≫ Functor.whiskerRight (α F j) J =
      projection F j ≫ ψ F j :=
  JTPrismChainGraphCover.parameter_projection (X F j) (ψ F j) (α F j)

/-- Every graph projection is an actual trivial fibration of simplicial sets. -/
theorem projection_trivialFibration (p : I F j) :
    trivialFibrations SSet.{0} ((projection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration (X F j) (ψ F j) (α F j)
    (JTJointPairChainDiagram.toOriginal_surjective F j) p

end
end DaggerModels.PartII.JTJointPairGapChainGraph
