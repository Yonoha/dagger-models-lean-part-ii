import DaggerModelsPartII.JTParametricRelativeExtension
import DaggerModelsPartII.JTHigherInterleavedParameter
import DaggerModelsPartII.JTInjectiveOrderedEndpointFibration

/-!
# Higher relative extension over the literal ordered endpoint arrow
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTHigherEndpointExtension

open JTHigherInterleavedParameter

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

/-- Extend the whole specified time subcomplex and the whole overlap to one
ordered coefficient, retaining the projection to the original base. -/
theorem exists_extension (k n : SimplexCategory) {A L X Y : SSet.{u}}
    (i : A ⟶ simplex k) [Mono i] (j : L ⟶ simplex n) [Mono j]
    (p : X ⟶ Y) [Fibration p]
    (h : WeakEquivalence i ∨ WeakEquivalence j ∨ WeakEquivalence p)
    (b : simplex k ⟶ Y)
    (gB : simplex k ⊗ L ⟶ X) (gA : A ⊗ simplex n ⟶ X)
    (hcompat : (i ▷ L) ≫ gB = (A ◁ j) ≫ gA)
    (hB : gB ≫ p = (simplex k ◁ j) ≫ fst (simplex k) (simplex n) ≫ b)
    (hA : gA ≫ p = (i ▷ simplex n) ≫ fst (simplex k) (simplex n) ≫ b) :
    ∃ E : simplex (common k n) ⟶ X,
      (simplex k ◁ j) ≫ prism k n ≫ E = gB ∧
      (i ▷ simplex n) ≫ prism k n ≫ E = gA ∧
      E ≫ p = SSet.stdSimplex.map (ret k n) ≫ b := by
  obtain ⟨F, hFB, hFA, hF⟩ := JTParametricRelativeExtension.exists_extension
    i j p h (fst (simplex k) (simplex n) ≫ b) gB gA hcompat hB hA
  letI : Cofibration (prism.{u} k n) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  letI := prism_weak.{u} k n
  let c : CommSq F (prism k n) p (SSet.stdSimplex.map (ret k n) ≫ b) := by
    constructor
    rw [hF, ← Category.assoc, prism_ret]
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · rw [c.fac_left, hFB]
  · rw [c.fac_left, hFA]

open SegalLocalizers JTProjectiveOrderedFiberComparison

/-- For the actual pair of ordered cofaces, the entire time boundary and
all of a Kan weak monomorphic overlap may be prescribed simultaneously. -/
theorem exists_boundary_extension (k : SimplexCategory) (n : ℕ)
    (W : ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W)
    {A : SSet.{0}} (i : A ⟶ simplex k) [Mono i] [WeakEquivalence i]
    (b : simplex k ⟶ Limits.prod (row W ⦋0⦌) (row W ⦋0⦌))
    (gB : simplex k ⊗ (SSet.boundary n : SSet.{0}) ⟶ row W ⦋1⦌)
    (gA : A ⊗ simplex ⦋n⦌ ⟶ row W ⦋1⦌)
    (hcompat : (i ▷ (SSet.boundary n : SSet.{0})) ≫ gB =
      (A ◁ (SSet.boundary n).ι) ≫ gA)
    (hB : gB ≫ endpointArrow W =
      (simplex k ◁ (SSet.boundary n).ι) ≫ fst (simplex k) (simplex ⦋n⦌) ≫ b)
    (hA : gA ≫ endpointArrow W =
      (i ▷ simplex ⦋n⦌) ≫ fst (simplex k) (simplex ⦋n⦌) ≫ b) :
    ∃ E : simplex (common k ⦋n⦌) ⟶ row W ⦋1⦌,
      (simplex k ◁ (SSet.boundary n).ι) ≫ prism k ⦋n⦌ ≫ E = gB ∧
      (i ▷ simplex ⦋n⦌) ≫ prism k ⦋n⦌ ≫ E = gA ∧
      E ≫ endpointArrow W = SSet.stdSimplex.map (ret k ⦋n⦌) ≫ b := by
  letI := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact exists_extension k ⦋n⦌ i (SSet.boundary n).ι (endpointArrow W)
    (Or.inl inferInstance) b gB gA hcompat hB hA

end DaggerModels.PartII.JTHigherEndpointExtension
