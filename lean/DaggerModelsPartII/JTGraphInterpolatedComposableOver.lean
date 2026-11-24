import DaggerModelsPartII.JTGraphInterpolatedArrowOver
import DaggerModelsPartII.JTGraphTransportRestriction

/-! Three composable-arrow graph vertices and their exact edge faces. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedComposableOver

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphLiftRestriction (restrict)
open JTGraphInterpolatedComparison (Fiber sliceObject)
open JTGraphInterpolatedOverOriginal (overOriginal)
open JTGraphInterpolatedOverOriginalSlice (overOriginal_slice_iso)
open JTGraphTransportNaturality (toComma)
open JTGraphInterpolatedArrowOver (edgeFamily)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V Z : TargetComma Q} (a : U ⟶ V) (b : V ⟶ Z)
variable (D₀ : GraphLift U.left U.left.fiber.left)
  (D₁ : GraphLift V.left V.left.fiber.left)
  (D₂ : GraphLift Z.left Z.left.fiber.left)
variable (h₀ : D₀.collapse = 𝟙 _) (h₁ : D₁.collapse = 𝟙 _)
  (h₂ : D₂.collapse = 𝟙 _)

private abbrev source := U.left.fiber.left
private abbrev collapse := a.left.fiber.left ≫ b.left.fiber.left

/-- The three vertices in the original target over the original native source. -/
def triangleFamily : Fin (⦋2⦌.len + 1) → GraphLift Z.left U.left.fiber.left :=
  Fin.cases ((D₀.transport a.left).transport b.left)
    (Fin.cases ((restrict D₁ a.left.fiber.left).transport b.left)
      (fun _ ↦ restrict D₂ (a.left.fiber.left ≫ b.left.fiber.left)))

include h₀ h₁ h₂ in
theorem triangleFamily_collapse (i : Fin (⦋2⦌.len + 1)) :
    (triangleFamily a b D₀ D₁ D₂ i).collapse = collapse a b := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ ↦ ?_)) i
  · change (D₀.collapse ≫ a.left.fiber.left) ≫ b.left.fiber.left = _
    rw [h₀, Category.id_comp]
  · change (a.left.fiber.left ≫ D₁.collapse) ≫ b.left.fiber.left = _
    rw [h₁, Category.comp_id]
  · change (a.left.fiber.left ≫ b.left.fiber.left) ≫ D₂.collapse = _
    rw [h₂, Category.comp_id]

/-- The whole degree-two cylinder in the unchanged original comma slice. -/
def triangleOver : Fiber U.left.fiber.left ⦋2⦌ ⥤ Over Z :=
  overOriginal (collapse a b) (triangleFamily a b D₀ D₁ D₂)
    (triangleFamily_collapse a b D₀ D₁ D₂ h₀ h₁ h₂)

/-- Each original time slice has its exact graph predecessor in the slice. -/
def triangleSliceIso (i : Fin (⦋2⦌.len + 1)) :
    (triangleOver a b D₀ D₁ D₂ h₀ h₁ h₂).obj
      (sliceObject U.left.fiber.left ⦋2⦌ i) ≅
    Over.mk (toComma (triangleFamily a b D₀ D₁ D₂ i)) :=
  overOriginal_slice_iso (collapse a b) (triangleFamily a b D₀ D₁ D₂)
    (triangleFamily_collapse a b D₀ D₁ D₂ h₀ h₁ h₂) i

/-- First edge: transport the first arrow family along the second arrow. -/
theorem firstEdge (i : Fin (⦋1⦌.len + 1)) :
    triangleFamily a b D₀ D₁ D₂ ((SimplexCategory.δ (2 : Fin 3)).toOrderHom i) =
      (edgeFamily a D₀ D₁ i).transport b.left := by
  fin_cases i <;> rfl

/-- Second edge: restrict the second arrow family along the first source. -/
theorem secondEdge (i : Fin (⦋1⦌.len + 1)) :
    triangleFamily a b D₀ D₁ D₂ ((SimplexCategory.δ (0 : Fin 3)).toOrderHom i) =
      restrict (edgeFamily b D₁ D₂ i) a.left.fiber.left := by
  fin_cases i
  · exact (JTGraphTransportRestriction.transport_restrict D₁ a.left.fiber.left b).symm
  · rfl

/-- Long edge: the family for the composite original arrow. -/
theorem longEdge (i : Fin (⦋1⦌.len + 1)) :
    triangleFamily a b D₀ D₁ D₂ ((SimplexCategory.δ (1 : Fin 3)).toOrderHom i) =
      edgeFamily (a ≫ b) D₀ D₂ i := by
  fin_cases i
  · exact JTGraphLiftTransport.GraphLift.transport_comp D₀ a.left b.left |>.trans (by rfl)
  · change restrict D₂ (a.left.fiber.left ≫ b.left.fiber.left) =
      restrict D₂ (a ≫ b).left.fiber.left
    congr 1
    exact (BoundaryNecklaceComma.sourceCode
      (DecoratedCylinderNecklacePresentation.underDiagram W x y)).map_comp a.left b.left |>.symm

/-- Pointwise identification of the complete first face family. -/
theorem firstEdge_family :
    (fun i ↦ triangleFamily a b D₀ D₁ D₂
      ((SimplexCategory.δ (2 : Fin 3)).toOrderHom i)) =
    (fun i ↦ (edgeFamily a D₀ D₁ i).transport b.left) := by
  funext i
  exact firstEdge a b D₀ D₁ D₂ i

/-- Pointwise identification of the complete second face family. -/
theorem secondEdge_family :
    (fun i ↦ triangleFamily a b D₀ D₁ D₂
      ((SimplexCategory.δ (0 : Fin 3)).toOrderHom i)) =
    (fun i ↦ restrict (edgeFamily b D₁ D₂ i) a.left.fiber.left) := by
  funext i
  exact secondEdge a b D₀ D₁ D₂ i

/-- Pointwise identification of the complete long face family. -/
theorem longEdge_family :
    (fun i ↦ triangleFamily a b D₀ D₁ D₂
      ((SimplexCategory.δ (1 : Fin 3)).toOrderHom i)) =
    edgeFamily (a ≫ b) D₀ D₂ := by
  funext i
  exact longEdge a b D₀ D₁ D₂ i

end
end DaggerModels.PartII.JTGraphInterpolatedComposableOver
