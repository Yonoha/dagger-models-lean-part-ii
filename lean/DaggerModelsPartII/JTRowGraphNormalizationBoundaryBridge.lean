import DaggerModelsPartII.JTRowGraphNormalizationDiagram
import DaggerModelsPartII.JTHigherMixedGraphTargetLift
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv

/-!
# Boundary families from actual higher normalization simplices
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
  CartesianMonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphNormalizationBoundaryBridge

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTOrdinaryGraphNormalizationSpace JTHigherCommonMixedGraphFamilies
open JTFixedLiftSpaceTimeEquiv
open OrdinaryJTRealization JTReversalInput JTRowGraphFiber JTRowGraphNormalizationDiagram
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def side_boundary_of_time_simplex
    (W : Source) (k : SimplexCategory) (r : ℕ)
    (a : Fin (k.len + 1))
    (b : simplex k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌)
    (t : simplex ⦋0⦌ ⟶ row W ⦋1⦌)
    (sq : CommSq t (vertex k a) (endpointArrow W) b)
    (v : (SSet.ihomToPullbackFiber sq).obj (op ⦋r⦌)) :
    SideBoundary W k r a b t where
  map := (simplex k ◁ (SSet.boundary r).ι) ≫ timeMap sq ⦋r⦌ v
  over := by
    rw [Category.assoc, (timeMap_conditions sq ⦋r⦌ v).2]
  stationary := by
    calc
      (vertex k a ▷ SSet.boundary r) ≫
          ((simplex k ◁ (SSet.boundary r).ι) ≫ timeMap sq ⦋r⦌ v) =
        (simplex ⦋0⦌ ◁ (SSet.boundary r).ι) ≫
          ((vertex k a ▷ simplex ⦋r⦌) ≫ timeMap sq ⦋r⦌ v) := by
            rw [← Category.assoc, ← whisker_exchange, Category.assoc]
      _ = (simplex ⦋0⦌ ◁ (SSet.boundary r).ι) ≫
          (fst (simplex ⦋0⦌) (simplex ⦋r⦌) ≫ t) := by
            rw [(timeMap_conditions sq ⦋r⦌ v).1]
      _ = _ := rfl

/-- A literal higher simplex of the product normalization space gives the
two actual prescribed endpoint boundaries on the same mixed graph. -/
def boundaryFamiliesOfSimplex (W : Source) (d : ℕ) (k : SimplexCategory) (r : ℕ)
    (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x)
    (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) =
      rawVertex W y)
    (v : (space W ⦋d⦌ k f s x y hx hy).obj (op ⦋r⦌)) :
    BoundaryFamilies W d k r f s x y := by
  let vL := (prod.fst : space W ⦋d⦌ k f s x y hx hy ⟶
    leftSpace W ⦋d⦌ k f s x hx).app (op ⦋r⦌) v
  let vR := (prod.snd : space W ⦋d⦌ k f s x y hx hy ⟶
    rightSpace W ⦋d⦌ k f s y hy).app (op ⦋r⦌) v
  exact ⟨side_boundary_of_time_simplex W k r (graphIndex ⦋d⦌ k s 0)
    (prod.lift (SSet.stdSimplex.isTerminalObj₀.from (simplex k) ≫ vertexPoint W x)
      (f ≫ rowVertex W ⦋d⦌ 0))
    (vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (leftSquare W ⦋d⦌ k f s x hx) vL,
    side_boundary_of_time_simplex W k r (graphIndex ⦋d⦌ k s (Fin.last d))
      (prod.lift (f ≫ rowVertex W ⦋d⦌ (Fin.last d))
        (SSet.stdSimplex.isTerminalObj₀.from (simplex k) ≫ vertexPoint W y))
      (vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W)
      (rightSquare W ⦋d⦌ k f s y hy) vR⟩

/-- The higher simplex belongs to the actual diagram over one fixed raw
simplex, and its two time boundaries retain the graph's exact coefficient. -/
def boundaryFamiliesAt {W : Source} {d r : ℕ}
    {q : simplex ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
    (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)
    (G : Fiber q)
    (v : ((diagram hx hy).obj (op G)).obj (op ⦋r⦌)) :
    BoundaryFamilies W d G.obj.degree r (coefficient G) G.obj.parameter x y :=
  boundaryFamiliesOfSimplex W d G.obj.degree r (coefficient G) G.obj.parameter x y
    (leftEndpoint hx G) (rightEndpoint hy G) v

/-- A higher normalization simplex supplies the exact boundary data accepted
by the existing relative native-target lift. -/
theorem exists_relative_target_lift_of_simplex {W : Source} {d r : ℕ}
    {k : SimplexCategory} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
    (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x)
    (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) =
      rawVertex W y)
    {q : (single d).toSSet ⟶ realization.obj (ordinaryInput.obj W)}
    (hq : JTMixedGraphRawRefinement.nativeRawGraph W d k f s = q)
    (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (v : (space W ⦋d⦌ k f s x y hx hy).obj (op ⦋r⦌)) :
    ∃ E' : EdgeFamilies W ⦋d⦌ (JTHigherInterleavedParameter.common k ⦋r⦌)
        (SSet.stdSimplex.map (JTHigherInterleavedParameter.ret k ⦋r⦌) ≫ f)
        (s ≫ J.map (JTHigherInterleavedParameter.slice k ⦋r⦌ 0)) x y,
      (simplex k ◁ (SSet.boundary r).ι) ≫
          JTHigherInterleavedParameter.prism k ⦋r⦌ ≫ E'.left =
        (boundaryFamiliesOfSimplex W d k r f s x y hx hy v).left.map ∧
      (simplex k ◁ (SSet.boundary r).ι) ≫
          JTHigherInterleavedParameter.prism k ⦋r⦌ ≫ E'.right =
        (boundaryFamiliesOfSimplex W d k r f s x y hx hy v).right.map ∧
      ∃ U : (JTNecklaceEndpointCylinder.under (MixedGraphCylinderTraversal.code d)).obj ⦋r⦌ ⟶
        (JTTargetCommaPullback.diagram W x y
          (⟨single d, q, qx, qy⟩ : NecklacesOver
            (realization.obj (ordinaryInput.obj W)) (rawVertex W x) (rawVertex W y))).obj
          (OrderedLabelElements.mk W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            (MixedGraphCylinderTraversal.code d) (JTHigherInterleavedParameter.common k ⦋r⦌)
            (JTMixedGraphOrderedLabel.orderedPoint E')),
        U ≫ JTTargetCommaPullback.fst W x y
          (⟨single d, q, qx, qy⟩ : NecklacesOver
            (realization.obj (ordinaryInput.obj W)) (rawVertex W x) (rawVertex W y))
          (OrderedLabelElements.mk W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            (MixedGraphCylinderTraversal.code d) (JTHigherInterleavedParameter.common k ⦋r⦌)
            (JTMixedGraphOrderedLabel.orderedPoint E')) =
          JTHigherMixedGraphTargetLift.toDecorated d s ⦋r⦌ ∧
        U ≫ JTTargetCommaPullback.snd W x y
          (⟨single d, q, qx, qy⟩ : NecklacesOver
            (realization.obj (ordinaryInput.obj W)) (rawVertex W x) (rawVertex W y))
          (OrderedLabelElements.mk W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            (MixedGraphCylinderTraversal.code d) (JTHigherInterleavedParameter.common k ⦋r⦌)
            (JTMixedGraphOrderedLabel.orderedPoint E')) =
          JTHigherMixedGraphTargetLift.toNativeTarget d ⦋r⦌ := by
  obtain ⟨E', hL, hR, U, hF, hN⟩ :=
    JTHigherMixedGraphTargetLift.exists_relative_target_lift f s hq qx qy hW r
      (boundaryFamiliesOfSimplex W d k r f s x y hx hy v)
  exact ⟨E', hL, hR, U, hF, hN⟩

end

end DaggerModels.PartII.JTRowGraphNormalizationBoundaryBridge
