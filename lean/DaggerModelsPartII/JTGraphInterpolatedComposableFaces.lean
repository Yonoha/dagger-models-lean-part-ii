import DaggerModelsPartII.JTGraphInterpolatedComposableOver
import DaggerModelsPartII.JTGraphInterpolatedOverTime

/-!
# The three face functors in the slice over the final original object
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedComposableFaces

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphLiftRestriction (restrict)
open JTGraphInterpolatedOverOriginal (overOriginal)
open JTGraphInterpolatedOverTime (overOriginal_reindex)
open JTGraphInterpolatedArrowOver (edgeFamily edgeFamily_collapse comparisonOverArrow)
open JTGraphInterpolatedComposableOver
open JTNecklaceEndpointCylinder (under)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private theorem overOriginal_congr {Z : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
    {c c' : S ⟶ Z.left.fiber.left} {D D' : Fin (n.len + 1) → GraphLift Z.left S}
    (hD : ∀ i, (D i).collapse = c) (hD' : ∀ i, (D' i).collapse = c')
    (hc : c = c') (h : D = D') : overOriginal c D hD = overOriginal c' D' hD' := by
  subst c'
  subst D'
  rfl

variable {U V Z : TargetComma Q} (a : U ⟶ V) (b : V ⟶ Z)
variable (D₀ : GraphLift U.left U.left.fiber.left)
  (D₁ : GraphLift V.left V.left.fiber.left) (D₂ : GraphLift Z.left Z.left.fiber.left)
variable (h₀ : D₀.collapse = 𝟙 _) (h₁ : D₁.collapse = 𝟙 _) (h₂ : D₂.collapse = 𝟙 _)

private abbrev c := a.left.fiber.left ≫ b.left.fiber.left

include h₀ h₁ in
private theorem first_collapse (i : Fin (⦋1⦌.len + 1)) :
    ((edgeFamily a D₀ D₁ i).transport b.left).collapse = c a b :=
  congrArg (fun f ↦ f ≫ b.left.fiber.left) (edgeFamily_collapse a D₀ D₁ h₀ h₁ i)

include h₁ h₂ in
private theorem second_collapse (i : Fin (⦋1⦌.len + 1)) :
    (restrict (edgeFamily b D₁ D₂ i) a.left.fiber.left).collapse = c a b :=
  congrArg (fun f ↦ a.left.fiber.left ≫ f) (edgeFamily_collapse b D₁ D₂ h₁ h₂ i)

/-- The first face is the cylinder of the transported first edge family. -/
theorem firstFace :
    CostructuredArrow.map ((under U.left.fiber.left).map (SimplexCategory.δ (2 : Fin 3))) ⋙
      triangleOver a b D₀ D₁ D₂ h₀ h₁ h₂ =
    overOriginal (n := ⦋1⦌) (c a b) (fun i ↦ (edgeFamily a D₀ D₁ i).transport b.left)
      (first_collapse a b D₀ D₁ h₀ h₁) :=
  (overOriginal_reindex (c a b) (triangleFamily a b D₀ D₁ D₂)
    (triangleFamily_collapse a b D₀ D₁ D₂ h₀ h₁ h₂) (SimplexCategory.δ (2 : Fin 3))).trans
      (overOriginal_congr _ _ rfl (firstEdge_family a b D₀ D₁ D₂))

/-- The second face is the cylinder of the source-restricted second edge family. -/
theorem secondFace :
    CostructuredArrow.map ((under U.left.fiber.left).map (SimplexCategory.δ (0 : Fin 3))) ⋙
      triangleOver a b D₀ D₁ D₂ h₀ h₁ h₂ =
    overOriginal (n := ⦋1⦌) (c a b) (fun i ↦ restrict (edgeFamily b D₁ D₂ i) a.left.fiber.left)
      (second_collapse a b D₁ D₂ h₁ h₂) :=
  (overOriginal_reindex (c a b) (triangleFamily a b D₀ D₁ D₂)
    (triangleFamily_collapse a b D₀ D₁ D₂ h₀ h₁ h₂) (SimplexCategory.δ (0 : Fin 3))).trans
      (overOriginal_congr _ _ rfl (secondEdge_family a b D₀ D₁ D₂))

/-- The long face is exactly the original comparison for the composite arrow. -/
theorem longFace :
    CostructuredArrow.map ((under U.left.fiber.left).map (SimplexCategory.δ (1 : Fin 3))) ⋙
      triangleOver a b D₀ D₁ D₂ h₀ h₁ h₂ = comparisonOverArrow (a ≫ b) D₀ D₂ h₀ h₂ := by
  have hc : c a b = (a ≫ b).left.fiber.left :=
    ((BoundaryNecklaceComma.sourceCode
      (DecoratedCylinderNecklacePresentation.underDiagram W x y)).map_comp a.left b.left).symm
  exact (overOriginal_reindex (c a b) (triangleFamily a b D₀ D₁ D₂)
    (triangleFamily_collapse a b D₀ D₁ D₂ h₀ h₁ h₂) (SimplexCategory.δ (1 : Fin 3))).trans
      (overOriginal_congr _ _ hc (longEdge_family a b D₀ D₁ D₂))

end

end DaggerModels.PartII.JTGraphInterpolatedComposableFaces
