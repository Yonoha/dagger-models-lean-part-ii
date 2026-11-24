import DaggerModelsPartII.JTInjectiveOrderedEndpointFibration
import DaggerModelsPartII.ProjectiveInjectiveComparison
import DaggerModelsPartII.FibrationSquareWeakRecognition

/-! Recognition in the actual first row of the injectively fibrant reversal diagram. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFirstRowWeakRecognition

open SegalLocalizers JTProjectiveOrderedFiberComparison
open DaggerNativeSSetFibrationSquareFibreWeak

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The actual map on the original ordinary row of a reversal diagram. -/
def rowMap {W Z : Source} (f : W ⟶ Z) (m : SimplexCategory) :
    row W m ⟶ row Z m :=
  (JTRealizationDiagonal.ordinaryCurry.map (JTReversalInput.ordinaryInput.map f)).app (op m)

private theorem endpoint_square {W Z : Source} (f : W ⟶ Z) :
    endpointArrow W ≫ prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) =
      rowMap f ⦋1⦌ ≫ endpointArrow Z := by
  have h (i : Fin 2) : endpoint W i ≫ rowMap f ⦋0⦌ =
      rowMap f ⦋1⦌ ≫ endpoint Z i :=
    (JTRealizationDiagonal.ordinaryCurry.map (JTReversalInput.ordinaryInput.map f)).naturality
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op
  apply prod.hom_ext
  · simpa only [endpointArrow, prod.lift_fst, prod.lift_fst_assoc,
      prod.map_fst, Category.assoc] using h 0
  · simpa only [endpointArrow, prod.lift_snd, prod.lift_snd_assoc,
      prod.map_snd, Category.assoc] using h 1

private theorem prod_diagonal_weak {A B : SSet.{0}} (f : A ⟶ B)
    [IsFibrant A] [IsFibrant B] [WeakEquivalence f] :
    WeakEquivalence (prod.map f f) := by
  haveI : WeakEquivalence (prod.map f (𝟙 A)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f A).flip
  haveI : WeakEquivalence (prod.map f (𝟙 B)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f B).flip
  have h : prod.map (𝟙 B) f =
      (prod.braiding B A).hom ≫ prod.map f (𝟙 B) ≫ (prod.braiding B B).hom := by
    apply prod.hom_ext <;> simp
  haveI : WeakEquivalence (prod.map (𝟙 B) f) := by rw [h]; infer_instance
  have hcomp : prod.map f (𝟙 A) ≫ prod.map (𝟙 B) f = prod.map f f := by
    simp only [prod.map_map, Category.comp_id, Category.id_comp]
  rw [← hcomp]
  infer_instance

private theorem row_fibrant (W : Source) [IsFibrant W] (m : SimplexCategory) :
    IsFibrant (row W m) := by
  have h := ProjectiveInjectiveComparison.isFibrant_projective ReverseSimplexᵒᵖ W
    (show IsFibrant W from inferInstance)
  haveI := (ProjectiveKanDiagram.model_isFibrant_iff ReverseSimplexᵒᵖ W).mp h
    (op (ReverseSimplex.inclusion.obj m))
  exact (isFibrant_iff_of_isTerminal
    ((rowRestrictionIso W m).hom ≫ terminal.from _) terminalIsTerminal).mpr inferInstance

/-- For maps of injectively fibrant reversal diagrams, weakness of the
zero row and of the literal ordered endpoint fibers detects weakness of
the first row. -/
theorem rowOne_weak {W Z : Source} (f : W ⟶ Z) [IsFibrant W] [IsFibrant Z]
    [WeakEquivalence (rowMap f ⦋0⦌)]
    (hf : ∀ x y : (row W ⦋0⦌).obj (op ⦋0⦌),
      WeakEquivalence (fibreMap (endpointArrow W) (endpointArrow Z)
        (rowMap f ⦋1⦌) (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌)) (endpoint_square f)
        (point W x y) (point W x y ≫ prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌)) rfl)) :
    WeakEquivalence (rowMap f ⦋1⦌) := by
  haveI := row_fibrant W ⦋0⦌
  haveI := row_fibrant Z ⦋0⦌
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W inferInstance
  haveI : Fibration (endpointArrow Z) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration Z inferInstance
  haveI : WeakEquivalence (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌)) :=
    prod_diagonal_weak (rowMap f ⦋0⦌)
  apply FibrationSquareWeakRecognition.weak_of_weak_base_and_vertex_fibers
    (endpointArrow W) (endpointArrow Z) (rowMap f ⦋1⦌) _ (endpoint_square f)
  intro b
  let x := SSet.yonedaEquiv (b ≫ prod.fst)
  let y := SSet.yonedaEquiv (b ≫ prod.snd)
  have hb : b = point W x y := by
    apply prod.hom_ext
    · simp only [point, prod.lift_fst, vertexPoint, x, Equiv.symm_apply_apply]
    · simp only [point, prod.lift_snd, vertexPoint, y, Equiv.symm_apply_apply]
  rw [hb]
  exact hf x y

end

end DaggerModels.PartII.JTFirstRowWeakRecognition
