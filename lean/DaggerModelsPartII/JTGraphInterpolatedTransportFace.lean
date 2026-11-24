import DaggerModelsPartII.JTGraphInterpolatedComposableFaces
import DaggerModelsPartII.JTGraphInterpolatedOverTransport

/-! The comparison from the original first edge to the first face. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedTransportFace

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphInterpolatedComposableOver (triangleOver)
open JTGraphInterpolatedComposableFaces (firstFace)
open JTGraphInterpolatedArrowOver (edgeFamily edgeFamily_collapse comparisonOverArrow)
open JTGraphInterpolatedOverTransport (overTransportComparison)
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

/-- In the slice over the last original object, the original first edge
maps to the first face by transport along the second arrow. -/
def firstFaceComparison :
    comparisonOverArrow a D₀ D₁ h₀ h₁ ⋙ Over.map b ⟶
      CostructuredArrow.map (S := necklaceUnder)
        ((under U.left.fiber.left).map (SimplexCategory.δ (2 : Fin 3))) ⋙
        triangleOver a b D₀ D₁ D₂ h₀ h₁ h₂ :=
  overTransportComparison (n := ⦋1⦌) a.left.fiber.left (edgeFamily a D₀ D₁)
      (edgeFamily_collapse a D₀ D₁ h₀ h₁) b ≫
    eqToHom (firstFace a b D₀ D₁ D₂ h₀ h₁ h₂).symm

end

end DaggerModels.PartII.JTGraphInterpolatedTransportFace
