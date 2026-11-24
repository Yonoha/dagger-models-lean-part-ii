import DaggerModelsPartII.JTGtildeOrderedFiberAction
import DaggerModelsPartII.ChosenHomotopyFiberFunctor
import OriginalSimplicialTrivialFibrationTensor

/-!
# The actual projective replacement on ordered chosen fibers

The functorial projective trivial fibration `p : Qproj W ⟶ W` induces a map
between the chosen homotopy fibers of the literal ordinary endpoint arrows.
Both row maps are Kan trivial fibrations, and their ordered product is Kan
trivial. The selected comparison therefore makes the chosen-fiber map weak
for every `W`, without imposing fibrancy on either raw endpoint arrow.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTProjectiveOrderedFiberComparison

open JTStrictificationMaps JTGtildeOrderedFiberAction
open ChosenHomotopyFiberComparison ChosenHomotopyFiberFunctor

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The literal original ordinary row of an arbitrary reversal diagram. -/
def row (W : Source) (m : SimplexCategory) : SSet.{0} :=
  (JTRealizationDiagonal.ordinaryCurry.obj
    (JTReversalInput.ordinaryInput.obj W)).obj (op m)

/-- An original ordered outer coface of the literal ordinary row. -/
def endpoint (W : Source) (i : Fin 2) : row W ⦋1⦌ ⟶ row W ⦋0⦌ :=
  (JTRealizationDiagonal.ordinaryCurry.obj
    (JTReversalInput.ordinaryInput.obj W)).map
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op

/-- The two literal outer cofaces in their original zero--one order. -/
def endpointArrow (W : Source) :
    row W ⦋1⦌ ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  prod.lift (endpoint W 0) (endpoint W 1)

/-- The specified degree-zero vertex of an ordinary row. -/
def vertexPoint (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ row W ⦋0⦌ :=
  SSet.yonedaEquiv.symm x

/-- The actual ordered pair of degree-zero row vertices. -/
def point (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  prod.lift (vertexPoint W x) (vertexPoint W y)

/-- The literal curry/restriction row is canonically the original reversal
diagram component, with the identity map in every vertical simplicial degree. -/
def rowRestrictionIso (W : Source) (m : SimplexCategory) :
    row W m ≅ W.obj (op (ReverseSimplex.inclusion.obj m)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    dsimp [row, JTRealizationDiagonal.ordinaryCurry,
      JTReversalInput.ordinaryInput]
    simp)

/-- The actual ordinary row of the projective replacement map. -/
def pRow (W : Source) (m : SimplexCategory) :
    sourceRow W m ⟶ row W m :=
  (JTRealizationDiagonal.ordinaryCurry.map
    (JTReversalInput.ordinaryInput.map (p.app W))).app (op m)

/-- The projective replacement map is a Kan trivial fibration on each
literal ordinary horizontal row. -/
theorem pRow_trivialFibration (W : Source) (m : SimplexCategory) :
    trivialFibrations SSet.{0} (pRow W m) := by
  letI : ModelCategory Source :=
    ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have hp := p_trivialFibration W
  change (ProjectiveKanDiagram.fibrations ReverseSimplexᵒᵖ ⊓
    ProjectiveKanDiagram.weakEquivalences ReverseSimplexᵒᵖ) (p.app W) at hp
  rw [ProjectiveKanDiagram.fibrations_inf_weakEquivalences] at hp
  let ea : Arrow.mk (pRow W m) ≅
      Arrow.mk ((p.app W).app (op (ReverseSimplex.inclusion.obj m))) :=
    Arrow.isoMk (rowRestrictionIso (Qproj.obj W) m)
      (rowRestrictionIso W m) (show _ = _ by ext k x; rfl)
  exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff ea).2
    (hp (op (ReverseSimplex.inclusion.obj m)))

/-- Naturality of the literal projective comparison at either ordered coface. -/
theorem pRow_endpoint (W : Source) (i : Fin 2) :
    sourceEndpoint W i ≫ pRow W ⦋0⦌ =
      pRow W ⦋1⦌ ≫ endpoint W i := by
  exact (JTRealizationDiagonal.ordinaryCurry.map
    (JTReversalInput.ordinaryInput.map (p.app W))).naturality
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op

/-- The actual ordered endpoint square of the projective replacement. -/
theorem endpoint_square (W : Source) :
    sourceEndpointArrow W ≫
      prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌) =
    pRow W ⦋1⦌ ≫ endpointArrow W := by
  apply prod.hom_ext
  · simpa only [sourceEndpointArrow, endpointArrow, prod.lift_fst, prod.lift_fst_assoc,
      prod.map_fst, Category.assoc] using pRow_endpoint W 0
  · simpa only [sourceEndpointArrow, endpointArrow, prod.lift_snd, prod.lift_snd_assoc,
      prod.map_snd, Category.assoc] using pRow_endpoint W 1

/-- The specified pair of source vertices maps to its actual image pair. -/
def targetVertices (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (row W ⦋0⦌).obj (op ⦋0⦌) ×
      (row W ⦋0⦌).obj (op ⦋0⦌) :=
  ((pRow W ⦋0⦌).app (op ⦋0⦌) x,
    (pRow W ⦋0⦌).app (op ⦋0⦌) y)

/-- The ordered point square is the Yoneda image of the actual projective map. -/
theorem point_square (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    sourcePoint W x y ≫
      prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌) =
    point W (targetVertices W x y).1 (targetVertices W x y).2 := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc]
    simp only [sourcePoint, point, prod.lift_fst]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, sourceVertexPoint, vertexPoint,
      Equiv.apply_symm_apply]
    rfl
  · rw [Category.assoc, prod.map_snd, ← Category.assoc]
    simp only [sourcePoint, point, prod.lift_snd]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, sourceVertexPoint, vertexPoint,
      Equiv.apply_symm_apply]
    rfl

/-- The actual map on chosen fibers of the two literal ordered endpoint
arrows, with its source point and the target point determined by `p`. -/
def chosenFiberMap (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    chosenFiber (sourceEndpointArrow W)
        (sourcePoint W x y) ⟶
      chosenFiber (endpointArrow W)
        (point W (targetVertices W x y).1 (targetVertices W x y).2) :=
  chosenMap (sourceEndpointArrow W)
    (endpointArrow W) (pRow W ⦋1⦌)
    (prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌)) (endpoint_square W)
    (sourcePoint W x y)
    (point W (targetVertices W x y).1 (targetVertices W x y).2)
    (point_square W x y)

/-- The literal first-row map is Kan weak. -/
private theorem pOne_weak (W : Source) :
    WeakEquivalence (pRow W ⦋1⦌) :=
  ((mem_trivialFibrations_iff _).1 (pRow_trivialFibration W ⦋1⦌)).2

/-- The map on the actual ordered product of zero rows is Kan weak. -/
private theorem pBase_weak (W : Source) :
    WeakEquivalence (prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌)) :=
  ((mem_trivialFibrations_iff _).1
    (DaggerOriginalSimplicialTrivialFibrationTensor.prodMap_trivialFibration
      (pRow W ⦋0⦌) (pRow W ⦋0⦌)
      (pRow_trivialFibration W ⦋0⦌)
      (pRow_trivialFibration W ⦋0⦌))).2

/-- The chosen projective-replacement action is Kan weak for every `W`.
No fibrancy of the raw ordered endpoint arrow or of `W` is required. -/
theorem chosenFiberMap_weak (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (chosenFiberMap W x y) := by
  let a := sourceEndpointArrow W
  let b := endpointArrow W
  let f := pRow W ⦋1⦌
  let g := prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌)
  let z := sourcePoint W x y
  let w := point W (targetVertices W x y).1 (targetVertices W x y).2
  letI : WeakEquivalence f := pOne_weak W
  letI : WeakEquivalence g := pBase_weak W
  letI : Fibration (replacement b).p :=
    (fibration_iff _).mpr (replacement b).hp
  letI : WeakEquivalence (replacement b).i :=
    (weakEquivalence_iff _).mpr (replacement b).hi.2
  have hfi : WeakEquivalence (f ≫ (replacement b).i) := inferInstance
  have h : a ≫ g = (f ≫ (replacement b).i) ≫ (replacement b).p := by
    rw [Category.assoc, (replacement b).fac]
    exact endpoint_square W
  change WeakEquivalence
    (comparison a (replacement b).p (f ≫ (replacement b).i) g
      h z w (point_square W x y))
  exact comparison_weak a (replacement b).p (f ≫ (replacement b).i) g
    h z w (point_square W x y)

end

end DaggerModels.PartII.JTProjectiveOrderedFiberComparison
