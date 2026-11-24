import DaggerModelsPartII.JTRawVertexRecovery
import DaggerModelsPartII.JTSimplexCoefficientExtension
import DaggerModelsPartII.JTEndpointNormalizationLifts

/-!
# The literal mixed graph supplies the original endpoint normalization squares
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTMixedGraphEndpointLifts

open OrdinaryJTRealization JTRealizationGenerators JTReversalInput
open JTProjectiveOrderedFiberComparison JTParameterContraction JTRawVertexRecovery
open JTCylinderCEComparison (simplexUnit)
open JTEndpointNormalizationLifts JTSimplexCoefficientExtension

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The vertex selected by an ordinary zero-simplex operator. -/
def vertex (m : SimplexCategory) (i : Fin (m.len + 1)) :
    (Δ[0] : SSet.{0}) ⟶ Δ m :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ m i)

/-- Restrict the horizontal row to the selected vertex, at every parameter. -/
def rowVertex (W : Source) (m : SimplexCategory) (i : Fin (m.len + 1)) :
    row W m ⟶ row W ⦋0⦌ :=
  (JTRealizationDiagonal.ordinaryCurry.obj (ordinaryInput.obj W)).map
    (SimplexCategory.const ⦋0⦌ m i).op

/-- The actual parameter vertex of the graph at the specified horizontal vertex. -/
def graphIndex (m k : SimplexCategory) (s : Δ m ⟶ J k) (i : Fin (m.len + 1)) :
    Fin (k.len + 1) :=
  parameterIndex k (vertex m i ≫ s)

theorem graphIndex_vertex (m k : SimplexCategory) (s : Δ m ⟶ J k)
    (i : Fin (m.len + 1)) :
    vertex m i ≫ s = parameterVertex k (graphIndex m k s i) := by
  rw [← JTParameterVertexKan.simplexUnit_vertex]
  exact parameterIndex_vertex k _

/-- The original raw graph map. The parameter map may be nonmonotone on objects. -/
def rawGraph (W : Source) (m k : SimplexCategory) (f : Δ k ⟶ row W m)
    (s : Δ m ⟶ J k) : Δ m ⟶ R W :=
  CartesianMonoidalCategory.lift (𝟙 (Δ m)) s ≫
    generator (ordinaryInput.obj W) (m, k) (SSet.yonedaEquiv (X := row W m) f)

/-- The literal row vertex determined by the horizontal and parameter faces. -/
def graphRowVertex (W : Source) (m k : SimplexCategory)
    (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k) (i : Fin (m.len + 1)) :
    (row W ⦋0⦌).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (vertex k (graphIndex m k s i) ≫ f ≫ rowVertex W m i)

theorem rawGraph_vertex (W : Source) (m k : SimplexCategory) (f : Δ k ⟶ row W m)
    (s : Δ m ⟶ J k) (i : Fin (m.len + 1)) :
    SSet.yonedaEquiv (vertex m i ≫ rawGraph W m k f s) =
      rawVertex W (graphRowVertex W m k f s i) := by
  let a : (⦋0⦌, ⦋0⦌) ⟶ (m, k) := (SimplexCategory.const ⦋0⦌ m i,
    SimplexCategory.const ⦋0⦌ k (graphIndex m k s i))
  let w := SSet.yonedaEquiv (X := row W m) f
  have hbox : SSet.yonedaEquiv
      (vertex m i ≫ CartesianMonoidalCategory.lift (𝟙 (Δ m)) s) = boxVertex a := by
    rw [boxVertex_formula]
    change (SSet.yonedaEquiv (vertex m i ≫ 𝟙 (Δ m)),
      SSet.yonedaEquiv (vertex m i ≫ s)) = _
    rw [Category.comp_id, vertex, SSet.stdSimplex.yonedaEquiv_map]
    apply Prod.ext
    · rfl
    · exact congrArg SSet.yonedaEquiv (parameterIndex_vertex k _)
  have hrow : (ordinaryInput.obj W).map a.op w = graphRowVertex W m k f s i := by
    unfold graphRowVertex vertex
    rw [SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_comp]
    simp [a, w, rowVertex, row, JTRealizationDiagonal.ordinaryCurry,
      JTReversalInput.ordinaryInput, Functor.uncurry, Functor.curry, Functor.curryObj]
  unfold rawGraph
  rw [← Category.assoc, SSet.yonedaEquiv_comp, hbox, generator_vertex, hrow]
  rfl

/-- For any strict extension of the central coefficient, its selected
horizontal face has the required raw endpoint as an actual row vertex. -/
theorem extendedGraphEndpoint (W : Source) (m k : SimplexCategory)
    (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k) (z : J k ⟶ row W m)
    (hz : simplexUnit.app k ≫ z = f) (i : Fin (m.len + 1))
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : SSet.yonedaEquiv (vertex m i ≫ rawGraph W m k f s) = rawVertex W x) :
    parameterVertex k (graphIndex m k s i) ≫ z ≫ rowVertex W m i = vertexPoint W x := by
  have h := rawZeroGeneratorVertex_injective W ((rawGraph_vertex W m k f s i).symm.trans hx)
  rw [← JTParameterVertexKan.simplexUnit_vertex, Category.assoc, ← Category.assoc
    (simplexUnit.app k) z, hz]
  apply SSet.yonedaEquiv.injective
  exact h.trans (Equiv.apply_symm_apply _ _).symm

/-- Two edge coefficient families with the central coefficient's actual
boundary and the degenerate faces selected by the graph. -/
structure EdgeFamilies (W : Source) (m k : SimplexCategory)
    (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) where
  left : Δ k ⟶ row W ⦋1⦌
  right : Δ k ⟶ row W ⦋1⦌
  left_boundary : left ≫ endpointArrow W =
    prod.lift (SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫ vertexPoint W x)
      (f ≫ rowVertex W m 0)
  right_boundary : right ≫ endpointArrow W =
    prod.lift (f ≫ rowVertex W m (Fin.last m.len))
      (SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫ vertexPoint W y)
  left_degenerate : vertex k (graphIndex m k s 0) ≫ left =
    vertexPoint W x ≫ identityFamily W
  right_degenerate : vertex k (graphIndex m k s (Fin.last m.len)) ≫ right =
    vertexPoint W y ≫ identityFamily W

/-- The original injective fibrancy produces these complete families for
any mixed graph with the prescribed raw endpoint equations. -/
def chosenEdgeFamilies (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (m k : SimplexCategory) (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : SSet.yonedaEquiv (vertex m 0 ≫ rawGraph W m k f s) = rawVertex W x)
    (hy : SSet.yonedaEquiv (vertex m (Fin.last m.len) ≫ rawGraph W m k f s) =
      rawVertex W y) : EdgeFamilies W m k f s x y := by
  haveI := row_isFibrant W hW m
  let z := extend k f
  have hz : simplexUnit.app k ≫ z = f := extend_restrict k f
  let a := graphIndex m k s 0
  let b := graphIndex m k s (Fin.last m.len)
  let l := normalizedFamilies W hW k a a (z ≫ rowVertex W m 0) x x
    (extendedGraphEndpoint W m k f s z hz 0 x hx)
    (extendedGraphEndpoint W m k f s z hz 0 x hx)
  let r := normalizedFamilies W hW k b b (z ≫ rowVertex W m (Fin.last m.len)) y y
    (extendedGraphEndpoint W m k f s z hz (Fin.last m.len) y hy)
    (extendedGraphEndpoint W m k f s z hz (Fin.last m.len) y hy)
  refine ⟨leftSimplexFamily l, rightSimplexFamily r, ?_, ?_,
    leftSimplex_degenerate l, rightSimplex_degenerate r⟩
  · rw [leftSimplex_boundary, ← Category.assoc, hz]
  · rw [rightSimplex_boundary, ← Category.assoc, hz]

end

end DaggerModels.PartII.JTMixedGraphEndpointLifts
