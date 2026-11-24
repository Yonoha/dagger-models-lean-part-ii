import DaggerModelsPartII.JTGraphInterpolatedComposableFaces
import DaggerModelsPartII.JTGraphInterpolatedOverSource

/-! The comparison from the second face to the original second edge. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedSourceFace

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphInterpolatedComposableOver (triangleOver)
open JTGraphInterpolatedComposableFaces (secondFace)
open JTGraphInterpolatedArrowOver (edgeFamily edgeFamily_collapse comparisonOverArrow)
open JTGraphInterpolatedOverSource (overSourceComparison)
open JTGraphInterpolatedSourceComparison (sourceMap)
open JTNecklaceEndpointCylinder (under)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V Z : TargetComma Q} (a : U ⟶ V) (b : V ⟶ Z)
variable (D₀ : GraphLift U.left U.left.fiber.left)
  (D₁ : GraphLift V.left V.left.fiber.left) (D₂ : GraphLift Z.left Z.left.fiber.left)
variable (h₀ : D₀.collapse = 𝟙 _) (h₁ : D₁.collapse = 𝟙 _) (h₂ : D₂.collapse = 𝟙 _)

/-- In the slice over the last original object, the second face maps to the
original second edge along the native source map of the first arrow. -/
def secondFaceComparison :
    CostructuredArrow.map (S := necklaceUnder)
        ((under U.left.fiber.left).map (SimplexCategory.δ (0 : Fin 3))) ⋙
        triangleOver a b D₀ D₁ D₂ h₀ h₁ h₂ ⟶
      CostructuredArrow.map (S := necklaceUnder) (sourceMap a.left.fiber.left ⦋1⦌) ⋙
        comparisonOverArrow b D₁ D₂ h₁ h₂ :=
  eqToHom (secondFace a b D₀ D₁ D₂ h₀ h₁ h₂) ≫
    overSourceComparison (n := ⦋1⦌) b.left.fiber.left (edgeFamily b D₁ D₂)
      (edgeFamily_collapse b D₁ D₂ h₁ h₂) a.left.fiber.left

end

end DaggerModels.PartII.JTGraphInterpolatedSourceFace
