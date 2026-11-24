import DaggerModelsPartII.JTMixedGraphHorizontalLabel

/-!
# Horizontal restriction as an arrow in the original fixed-target comma

Both the full graph presentation and the native composite to the fixed raw
target are specified. The comparison can keep degeneracies of the middle bead.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTMixedGraphHorizontalEvaluation

open JTGraphRefinement JTMixedGraphHorizontalTraversal JTMixedGraphHorizontalLabel
open JTMixedGraphEndpointLifts
open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphOrderedLabel (orderedPoint)
open JTMixedGraphRawRefinement (nativeGraphParameter)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (n : SimplexCategory) := SSet.stdSimplex.{0}.obj n
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev code := MixedGraphCylinderTraversal.code

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev Target :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

variable (D : Refinement W x y Q) {T : NecklaceCode} (u : T ⟶ D.code)

private theorem traversal_eq :
    lift u.map (u.map ≫ D.parameter) ≫
        (JTNecklaceEndpointCylinder.cylinder D.code).app D.degree =
      u.map ≫ D.toComma.left.fiber.hom.right := by
  change lift u.map (u.map ≫ D.parameter) ≫
      (JTNecklaceEndpointCylinder.cylinder D.code).app D.degree =
    u.map ≫ lift (𝟙 D.code.toSSet) D.parameter ≫
      (JTNecklaceEndpointCylinder.cylinder D.code).app D.degree
  rw [← Category.assoc]
  congr 1

/-- Restrict an original graph in the same fixed-target comma. -/
def restrictComma : Target (Q := Q) :=
  JTGraphToPresentationArrow.graphToComma D.toComma T u u (u.map ≫ D.parameter) (traversal_eq D u)

/-- The specified native restriction is the internal operator of an actual comma arrow. -/
def restrictionArrow : restrictComma D u ⟶ D.toComma :=
  JTGraphToPresentationArrow.toComma Q D.toComma T u u (u.map ≫ D.parameter) (traversal_eq D u)

theorem restrictComma_native : (restrictComma D u).hom.hom = u ≫ D.collapse := rfl

theorem restrictionArrow_native : (restrictionArrow D u).left.fiber.left = u := rfl

section Horizontal

variable {d e : ℕ} {k : SimplexCategory}
variable {f : Δ k ⟶ row W ⦋e⦌} {s : Δ ⦋e⦌ ⟶ J.obj k}
variable (E : EdgeFamilies W ⦋e⦌ k f s x y)
variable (c : code e ⟶ Q.code)
variable (hc : realizeGraph W k (nativeGraphParameter s)
  (JTRealizedLabelEndpoints.orderedLabel W x y (code e) k (orderedPoint E)) = c.map ≫ Q.map)

private abbrev parent : Refinement W x y Q :=
  ⟨code e, k, orderedPoint E, nativeGraphParameter s, c, hc⟩

variable (a : ⦋d⦌ ⟶ ⦋e⦌)
variable (h₀ : a.toOrderHom 0 = 0) (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)

private abbrev pad := padded (singleOperator a h₀ h₁)

/-- The horizontal restriction evaluates over the unchanged raw target. -/
abbrev horizontal := restrictComma (parent E c hc) (pad a h₀ h₁)

/-- Its actual ordered label and traversal are precisely those of the
horizontally restricted row graph, with both original padded endpoints. -/
theorem horizontal_presentation :
    (horizontal E c hc a h₀ h₁).left =
      presentation W x y (code d) k (orderedPoint (restrictFamilies a h₀ h₁ E))
        (nativeGraphParameter (SSet.stdSimplex.map a ≫ s)) := by
  change presentation W x y (code d) k
    (JTGraphToPresentationArrow.pulledLabel (parent E c hc).toComma.left (code d) (pad a h₀ h₁))
    ((pad a h₀ h₁).map ≫ nativeGraphParameter s) = _
  have h := orderedPoint_horizontal a h₀ h₁ E
  change JTGraphToPresentationArrow.pulledLabel
    (parent E c hc).toComma.left (code d) (pad a h₀ h₁) =
      orderedPoint (restrictFamilies a h₀ h₁ E) at h
  rw [h, parameter_horizontal]

/-- The actual native leg is the prescribed padded operator followed by the parent's leg. -/
theorem horizontal_native :
    (horizontal E c hc a h₀ h₁).hom.hom = pad a h₀ h₁ ≫ c := rfl

/-- Compare both exact evaluations inside the original fixed-target comma. -/
abbrev horizontalArrow :
    horizontal E c hc a h₀ h₁ ⟶ (parent E c hc).toComma :=
  restrictionArrow (parent E c hc) (pad a h₀ h₁)

end Horizontal

end

end DaggerModels.PartII.JTMixedGraphHorizontalEvaluation
