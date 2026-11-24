import RelativeHornFillingReversal
import OriginalRightOuterHornInclusions
import OriginalHomotopyCategoryOppositeComparison
import OriginalOrdinaryKanCoreEdgeMembership

/-!
# The first edge of the literal left outer horn

The face omitting the final vertex gives a concrete inclusion of the first
edge into `Λ[k+2,0]`. Its ambient map selects the literal vertices `0,1`.
Finite ordinal reversal identifies this operator with the original native
right-block last-edge operator. This is the geometric calibration required
before transporting selected right-outer-horn fillers through reversal.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerOriginalStandardSimplexReversal DaggerOriginalHornReversal
open DaggerOriginalOrdinaryKanCoreEdgeMembership

universe u

namespace DaggerModels.PartII.RelativeLeftOuterHornGeometry

noncomputable section

/-- The native ordinal map selecting the original first edge. -/
def firstEdgeHom (k : ℕ) : ⦋1⦌ ⟶ ⦋k + 2⦌ :=
  pairOperator (0 : Fin (k + 3)) (1 : Fin (k + 3))
    (by change (0 : ℕ) ≤ 1; omega)

private theorem last_ne_zero (k : ℕ) :
    (Fin.last (k + 2) : Fin (k + 3)) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_zero] at hv
  omega

/-- The actual first edge lies in the left outer horn through the
coface omitting the final vertex. -/
def firstEdgeInclusion (k : ℕ) :
    (Δ[1] : SSet.{u}) ⟶ (Λ[k + 2, (0 : Fin (k + 3))] : SSet.{u}) :=
  SSet.stdSimplex.map
      (pairOperator (0 : Fin (k + 2)) (1 : Fin (k + 2))
        (by change (0 : ℕ) ≤ 1; omega)) ≫
    SSet.horn.ι (0 : Fin (k + 3)) (Fin.last (k + 2)) (last_ne_zero k)

/-- The ambient map of that inclusion is the literal original first edge. -/
theorem firstEdgeInclusion_comp (k : ℕ) :
    firstEdgeInclusion.{u} k ≫ Λ[k + 2, (0 : Fin (k + 3))].ι =
      SSet.stdSimplex.map (firstEdgeHom k) := by
  rw [firstEdgeInclusion, Category.assoc, SSet.horn.ι_ι]
  change SSet.stdSimplex.map
      (pairOperator (0 : Fin (k + 2)) (1 : Fin (k + 2)) _) ≫
      SSet.stdSimplex.map (SimplexCategory.δ (Fin.last (k + 2))) =
        SSet.stdSimplex.map (firstEdgeHom k)
  rw [← Functor.map_comp]
  congr 1
  ext j
  fin_cases j <;> rfl

/-- Reversing the first-edge ordinal operator gives exactly the native
right-block last-edge operator, with no endpoint substitution. -/
theorem reverse_firstEdgeHom (k : ℕ) :
    SimplexCategory.rev.map (firstEdgeHom k) =
      AugmentedSimplexCategory.inr' ⦋k⦌ ⦋1⦌ := by
  ext j
  fin_cases j
  · rw [SimplexCategory.rev_map_apply]
    erw [AugmentedSimplexCategory.inr'_eval ⦋k⦌ ⦋1⦌ (0 : Fin 2)]
    simp [firstEdgeHom, pairOperator, Fin.val_rev]
  · rw [SimplexCategory.rev_map_apply]
    erw [AugmentedSimplexCategory.inr'_eval ⦋k⦌ ⦋1⦌ (1 : Fin 2)]
    simp [firstEdgeHom, pairOperator]

/-- Reversal of standard simplices is natural for every native operator. -/
private theorem simplexReversal_natural_aux {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.stdSimplex.map f ≫ standardSimplexReversalInv n =
      standardSimplexReversalInv m ≫
        SSet.opFunctor.map (SSet.stdSimplex.map (SimplexCategory.rev.map f)) := by
  ext q s
  apply SSet.opObjEquiv.injective
  apply SSet.stdSimplex.objEquiv.injective
  change SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s ≫ f) =
    SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s) ≫
      SimplexCategory.rev.map f
  exact Functor.map_comp _ _ _

/-- Reversal of standard simplices is natural for the exact last-edge map. -/
private theorem simplexReversal_natural (k : ℕ) :
    SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋1⦌) ≫
        standardSimplexReversalInv (k + 2) =
      standardSimplexReversalInv 1 ≫
        SSet.opFunctor.map (SSet.stdSimplex.map (firstEdgeHom k)) := by
  have hrev : SimplexCategory.rev.map
      (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋1⦌) = firstEdgeHom k := by
    rw [← reverse_firstEdgeHom k, reverse_operator_twice]
  simpa only [hrev] using simplexReversal_natural_aux
    (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋1⦌)

/-- At the ambient simplex level, the exact right-horn last edge reverses
to the exact left-horn first edge. The two horn inclusions are retained. -/
theorem reversed_edge_ambient (k : ℕ) :
    DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion.{u} k ≫
        (Λ[k + 2, Fin.last (k + 2)] :
          (Δ[k + 2] : SSet.{u}).Subcomplex).ι ≫
          standardSimplexReversalInv (k + 2) =
      standardSimplexReversalInv 1 ≫
        SSet.opFunctor.map
          (firstEdgeInclusion.{u} k ≫
            (Λ[k + 2, (0 : Fin (k + 3))] :
              (Δ[k + 2] : SSet.{u}).Subcomplex).ι) := by
  rw [← Category.assoc,
    DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion_comp]
  rw [firstEdgeInclusion_comp]
  exact simplexReversal_natural k

#print axioms firstEdgeInclusion_comp
#print axioms reverse_firstEdgeHom
#print axioms reversed_edge_ambient

end

end DaggerModels.PartII.RelativeLeftOuterHornGeometry
