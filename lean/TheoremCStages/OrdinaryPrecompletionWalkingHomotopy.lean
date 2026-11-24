import OrdinaryPrecompletionBinaryProducts
import OrdinaryWalkingPrecompletionRows

/-!
# Actual walking homotopies after corrected precompletion

The walking rows are Kan and contractible, so the original product projection
becomes a rowwise weak equivalence. Its actual vertex sections do too. Thus a
homotopy through the same product preserves rowwise weakness of the two end maps.
This does not assert Segal recognition or completeness of a replacement.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionWalkingHomotopy

open OrdinaryCSSLocalization (Space walkingSpace)
open OrdinarySegalVerticalPrecompletionNaturality (precompletionMap)
open OrdinarySegalVerticalPrecompletion (precompletion)

noncomputable section

private theorem product_row_fst_weak (W V : Space) (n : SimplexCategory)
    (hKan : (V.obj (op n)).KanComplex)
    (hWeak : WeakEquivalence (terminal.from (V.obj (op n)))) :
    WeakEquivalence ((prod.fst : W ⨯ V ⟶ W).app (op n)) := by
  have : (V.obj (op n)).KanComplex := hKan
  have : Fibration (terminal.from (V.obj (op n))) := inferInstance
  have ht := (mem_trivialFibrations_iff (terminal.from (V.obj (op n)))).mpr
    ⟨inferInstance, hWeak⟩
  have hp : trivialFibrations SSet.{0}
      (prod.fst : W.obj (op n) ⨯ V.obj (op n) ⟶ W.obj (op n)) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_isLimit_binaryFan_of_isTerminal
        (limit.isLimit (pair (W.obj (op n)) (V.obj (op n)))) terminalIsTerminal).flip ht
  have : WeakEquivalence
      (prod.fst : W.obj (op n) ⨯ V.obj (op n) ⟶ W.obj (op n)) :=
    ((mem_trivialFibrations_iff _).mp hp).2
  let ev := (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op n)
  have : IsIso (prodComparison ev W V) := inferInstance
  have h : prodComparison ev W V ≫ prod.fst =
      (prod.fst : W ⨯ V ⟶ W).app (op n) := prodComparison_fst ev W V
  have : WeakEquivalence (prodComparison ev W V) := inferInstance
  have : WeakEquivalence (prod.fst : ev.obj W ⨯ ev.obj V ⟶ ev.obj W) :=
    ((mem_trivialFibrations_iff _).mp hp).2
  rw [← h]
  infer_instance

/-- The original projection becomes weak in every actual horizontal row. -/
theorem projection_row_weak (W : Space) (n : SimplexCategory) :
    WeakEquivalence
      ((precompletionMap (prod.fst : W ⨯ walkingSpace ⟶ W)).app (op n)) := by
  have hp : WeakEquivalence
      ((prod.fst : precompletion W ⨯ precompletion walkingSpace ⟶
        precompletion W).app (op n)) :=
    product_row_fst_weak _ _ n (OrdinaryWalkingPrecompletionRows.row_kan n)
      (OrdinaryWalkingPrecompletionRows.row_toTerminal_weak n)
  have h : (OrdinaryPrecompletionBinaryProducts.productIso W walkingSpace).hom.app (op n) ≫
      (prod.fst : precompletion W ⨯ precompletion walkingSpace ⟶
        precompletion W).app (op n) =
      (precompletionMap (prod.fst : W ⨯ walkingSpace ⟶ W)).app (op n) :=
    congrArg (fun f ↦ f.app (op n))
      (OrdinaryPrecompletionBinaryProducts.productIso_fst W walkingSpace)
  have : WeakEquivalence
      ((OrdinaryPrecompletionBinaryProducts.productIso W walkingSpace).hom.app (op n)) :=
    inferInstance
  rw [← h]
  infer_instance

/-- Keep the actual specified walking vertex in the original product section. -/
def vertexSection (W : Space) (v : (⊤_ Space) ⟶ walkingSpace) :
    W ⟶ W ⨯ walkingSpace :=
  prod.lift (𝟙 W) (terminal.from W ≫ v)

/-- Every specified walking-vertex section becomes rowwise weak. -/
theorem vertexSection_row_weak (W : Space) (v : (⊤_ Space) ⟶ walkingSpace)
    (n : SimplexCategory) :
    WeakEquivalence ((precompletionMap (vertexSection W v)).app (op n)) := by
  have : WeakEquivalence
      ((precompletionMap (prod.fst : W ⨯ walkingSpace ⟶ W)).app (op n)) :=
    projection_row_weak W n
  have hs : vertexSection W v ≫ (prod.fst : W ⨯ walkingSpace ⟶ W) = 𝟙 W := by
    simp only [vertexSection, prod.lift_fst]
  have h := congrArg (fun f ↦ f.app (op n))
    (OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_comp
      (vertexSection W v) (prod.fst : W ⨯ walkingSpace ⟶ W))
  rw [hs, OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_id] at h
  exact weakEquivalence_of_postcomp_of_fac h.symm

/-- An actual walking homotopy preserves rowwise weakness after precompletion. -/
theorem homotopy_row_weak_iff {W V : Space}
    (v₀ v₁ : (⊤_ Space) ⟶ walkingSpace) (H : W ⨯ walkingSpace ⟶ V)
    (n : SimplexCategory) :
    WeakEquivalence ((precompletionMap (vertexSection W v₀ ≫ H)).app (op n)) ↔
      WeakEquivalence ((precompletionMap (vertexSection W v₁ ≫ H)).app (op n)) := by
  have : WeakEquivalence ((precompletionMap (vertexSection W v₀)).app (op n)) :=
    vertexSection_row_weak W v₀ n
  have : WeakEquivalence ((precompletionMap (vertexSection W v₁)).app (op n)) :=
    vertexSection_row_weak W v₁ n
  simp only [OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_comp,
    NatTrans.comp_app]
  rw [weakEquivalence_precomp_iff, weakEquivalence_precomp_iff]

#print axioms projection_row_weak
#print axioms vertexSection_row_weak
#print axioms homotopy_row_weak_iff

end

end DaggerModels.PartII.OrdinaryPrecompletionWalkingHomotopy
