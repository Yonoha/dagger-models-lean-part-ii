import OrdinaryAllVertexSquareComparison
import OrdinarySegalLocalization

/-!
# Segal recognition from all ordered-vertex squares

This reduction takes weakness of the actual all-vertex comparisons as an
explicit hypothesis. It does not assume that the relative target is Segal.
The comparison is then rowwise weak, and locality of fibrant objects transfers
the Segal condition from the source to the relative target.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryRelativeSegalRecognitionReduction

open OrdinaryCSSLocalization (Space)
open OrdinaryZeroCoskeleton (relativeComparison targetOverZero)
open OrdinaryAllVertexSquareComparison

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- All original ordered-vertex squares being homotopy cartesian makes the
literal relative zero-row comparison levelwise weak. -/
theorem relativeComparison_weak_of_vertexComparisons
    {W Z : Space} (f : W ⟶ Z)
    (hCart : ∀ n : ℕ, WeakEquivalence (vertexComparison f n)) :
    WeakEquivalence (relativeComparison f) := by
  apply (weakEquivalence_iff (relativeComparison f)).mpr
  rw [InjectiveKanDiagram.model_weakEquivalences]
  intro j
  cases j using Opposite.rec with
  | op j =>
    induction j using SimplexCategory.rec with
    | _ n =>
      letI : WeakEquivalence (vertexComparison f n) := hCart n
      exact (weakEquivalence_iff _).mp
        (weakEquivalence_of_postcomp_of_fac
          (relativeComparison_vertexComparison f n))

/-- A weak equivalence between injectively fibrant ordinary spaces preserves
the exact strict spine tests. This uses the checked local-object invariance
theorem for the spine family. -/
theorem segalCondition_iff_of_weak {W Z : Space}
    [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z)
    (hf : WeakEquivalence f) :
    OrdinaryCSSConditions.segalCondition W ↔
      OrdinaryCSSConditions.segalCondition Z := by
  have hlocal : Localization.localObject
      OrdinarySegalLocalization.localizingFamily W ↔
      Localization.localObject
        OrdinarySegalLocalization.localizingFamily Z :=
    Localization.localObject_iff_of_weak
      OrdinarySegalLocalization.localizingFamily f
      ((weakEquivalence_iff f).mp hf)
  constructor
  · intro hW
    have h : Localization.localObject
        OrdinarySegalLocalization.localizingFamily W :=
      (OrdinarySegalLocalization.localObject_iff_strict W).mpr
        ⟨inferInstance, hW⟩
    exact ((OrdinarySegalLocalization.localObject_iff_strict Z).mp
      (hlocal.mp h)).2
  · intro hZ
    have h : Localization.localObject
        OrdinarySegalLocalization.localizingFamily Z :=
      (OrdinarySegalLocalization.localObject_iff_strict Z).mpr
        ⟨inferInstance, hZ⟩
    exact ((OrdinarySegalLocalization.localObject_iff_strict W).mp
      (hlocal.mpr h)).2

/-- Segalness of the relative target follows from the source Segal condition
and weakness of the original all-vertex comparisons. -/
theorem targetOverZero_segal_of_vertexComparisons
    {W Z : Space} [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z)
    (hW : OrdinaryCSSConditions.segalCondition W)
    (hCart : ∀ n : ℕ, WeakEquivalence (vertexComparison f n)) :
    OrdinaryCSSConditions.segalCondition (targetOverZero f) := by
  letI : IsFibrant (W.obj (op ⦋0⦌)) :=
    OrdinaryRelativeRowWeak.row_fibrant W (op ⦋0⦌)
  letI : IsFibrant (targetOverZero f) :=
    OrdinaryZeroCoskeleton.targetOverZero_fibrant f
  exact (segalCondition_iff_of_weak (relativeComparison f)
    (relativeComparison_weak_of_vertexComparisons f hCart)).mp hW

#print axioms relativeComparison_weak_of_vertexComparisons
#print axioms segalCondition_iff_of_weak
#print axioms targetOverZero_segal_of_vertexComparisons

end

end DaggerModels.PartII.OrdinaryRelativeSegalRecognitionReduction
