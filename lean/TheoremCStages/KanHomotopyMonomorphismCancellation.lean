import KanHomotopyMonomorphism
import NativeFibrationSurjectiveComponents
import NativeFibrationWeakFromVertexFibres

/-!
# Cancellation for Kan maps with weak strict diagonal

The argument is the public form of the relative-diagonal fiber calculation in
`DaggerModelsPartII/DiagonalRecognition.lean`, lines 455–539. Its source theorem
is private. The pullback comparison and the exact strict diagonal are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.KanHomotopyMonomorphismCancellation

noncomputable section

open KanHomotopyMonomorphism (diagonal)

/-- A weak strict diagonal makes the first self-pullback projection weak. -/
private theorem fst_weak_of_diagonal_weak {Y Z : SSet.{0}} (j : Y ⟶ Z)
    [WeakEquivalence (diagonal j)] : WeakEquivalence (pullback.fst j j) := by
  have h : diagonal j ≫ pullback.fst j j = 𝟙 Y := pullback.lift_fst _ _ _
  exact weakEquivalence_of_precomp_of_fac h

/-- Compare the fiber of the first self-pullback projection at `e` with the
actual fiber of `j` over `e ≫ j`. -/
private def fiberComparison {Y Z : SSet.{0}} (j : Y ⟶ Z)
    (e : (Δ[0] : SSet.{0}) ⟶ Y) :
    pullback (pullback.fst j j) e ⟶ pullback j (e ≫ j) :=
  pullback.lift
    (pullback.fst (pullback.fst j j) e ≫ pullback.snd j j)
    (pullback.snd (pullback.fst j j) e)
    (by
      rw [Category.assoc, ← pullback.condition]
      rw [← Category.assoc, pullback.condition, Category.assoc])

private def fiberComparisonInv {Y Z : SSet.{0}} (j : Y ⟶ Z)
    (e : (Δ[0] : SSet.{0}) ⟶ Y) :
    pullback j (e ≫ j) ⟶ pullback (pullback.fst j j) e :=
  pullback.lift
    (pullback.lift
      (pullback.snd j (e ≫ j) ≫ e)
      (pullback.fst j (e ≫ j))
      (by rw [Category.assoc, ← pullback.condition]))
    (pullback.snd j (e ≫ j))
    (by simp)

private theorem fiberComparison_left_inv {Y Z : SSet.{0}} (j : Y ⟶ Z)
    (e : (Δ[0] : SSet.{0}) ⟶ Y) :
    fiberComparison j e ≫ fiberComparisonInv j e =
      𝟙 (pullback (pullback.fst j j) e) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [fiberComparison, fiberComparisonInv, Category.assoc,
        pullback.condition]
    · simp [fiberComparison, fiberComparisonInv]
  · simp [fiberComparison, fiberComparisonInv]

private theorem fiberComparison_right_inv {Y Z : SSet.{0}} (j : Y ⟶ Z)
    (e : (Δ[0] : SSet.{0}) ⟶ Y) :
    fiberComparisonInv j e ≫ fiberComparison j e =
      𝟙 (pullback j (e ≫ j)) := by
  apply pullback.hom_ext <;> simp [fiberComparison, fiberComparisonInv]

private theorem fiberComparison_isIso {Y Z : SSet.{0}} (j : Y ⟶ Z)
    (e : (Δ[0] : SSet.{0}) ⟶ Y) : IsIso (fiberComparison j e) :=
  ⟨⟨fiberComparisonInv j e,
    fiberComparison_left_inv j e,
    fiberComparison_right_inv j e⟩⟩

/-- The actual vertex fiber of `j` above an image vertex is weakly a point. -/
private theorem imageFiber_weak {Y Z : SSet.{0}} (j : Y ⟶ Z)
    [Fibration j] [WeakEquivalence (diagonal j)]
    (e : (Δ[0] : SSet.{0}) ⟶ Y) :
    WeakEquivalence (pullback.snd j (e ≫ j)) := by
  haveI : WeakEquivalence (pullback.fst j j) :=
    fst_weak_of_diagonal_weak j
  letI : (trivialFibrations SSet.{0}).IsStableUnderBaseChange := by
    rw [← rlp_eq_of_wfs (cofibrations SSet.{0}) (trivialFibrations SSet.{0})]
    infer_instance
  have hr : trivialFibrations SSet.{0} (pullback.fst j j) :=
    (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩
  haveI : WeakEquivalence (pullback.snd (pullback.fst j j) e) :=
    (mem_trivialFibrations_iff _).mp
      ((trivialFibrations SSet.{0}).pullback_snd _ _ hr) |>.2
  haveI : IsIso (fiberComparison j e) := fiberComparison_isIso j e
  have h : fiberComparison j e ≫ pullback.snd j (e ≫ j) =
      pullback.snd (pullback.fst j j) e := by
    simp [fiberComparison]
  exact weakEquivalence_of_precomp_of_fac h

/-- A component-surjective Kan fibration with weak strict diagonal is weak. -/
theorem weak_of_diagonal_weak_of_components {Y Z : SSet.{0}} (j : Y ⟶ Z)
    [Fibration j] [WeakEquivalence (diagonal j)]
    (hπ : Function.Surjective (SSet.mapπ₀ j)) : WeakEquivalence j := by
  apply DaggerNativeFibrationWeakFromVertexFibres.weak_of_vertex_fibres_weak j
  intro b
  obtain ⟨e, he⟩ :=
    DaggerNativeFibrationSurjectiveComponents.vertices_surjective_of_components
      j hπ (SSet.yonedaEquiv b)
  let e' : (Δ[0] : SSet.{0}) ⟶ Y := SSet.yonedaEquiv.symm e
  have h : e' ≫ j = b := by
    apply SSet.yonedaEquiv.injective
    simpa only [e', SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using he
  rw [← h]
  exact imageFiber_weak j e'

/-- If a Kan fibration has weak strict diagonal and a weak composite through
it, both it and the preceding map are weak equivalences. -/
theorem weak_pair_of_composite_and_diagonal {X Y Z : SSet.{0}}
    (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    [Fibration j] [WeakEquivalence (i ≫ j)]
    [WeakEquivalence (diagonal j)] :
    WeakEquivalence j ∧ WeakEquivalence i := by
  letI : X.KanComplex := inferInstance
  letI : Z.KanComplex := inferInstance
  have hw := (SSet.weakEquivalence_iff_kanComplexW (i ≫ j)).mp inferInstance
  have hk : Function.Surjective (SSet.mapπ₀ (i ≫ j)) :=
    hw.bijective_mapπ₀.surjective
  have hjπ : Function.Surjective (SSet.mapπ₀ j) := by
    intro z
    obtain ⟨x, hx⟩ := hk z
    refine ⟨SSet.mapπ₀ i x, ?_⟩
    simpa only [SSet.mapπ₀_comp_apply] using hx
  haveI : WeakEquivalence j := weak_of_diagonal_weak_of_components j hjπ
  exact ⟨inferInstance, weakEquivalence_of_postcomp i j⟩

#print axioms weak_of_diagonal_weak_of_components
#print axioms weak_pair_of_composite_and_diagonal

end
end DaggerModels.PartII.KanHomotopyMonomorphismCancellation
