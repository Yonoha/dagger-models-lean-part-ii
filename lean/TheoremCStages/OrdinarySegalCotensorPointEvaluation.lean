import OrdinarySegalHorizontalCotensorPoint

/-!
# Actual evaluation at a horizontal parameter vertex

The original vertex restriction is followed by the checked point-parameter
isomorphism. Its strict section is the unchanged constant section, and the
opposite composite is restriction by the actual constant parameter map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCotensorPointEvaluation

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre evaluateVertex)
open OrdinarySegalHorizontalCotensorPoint (pointIso constantSection)

noncomputable section

/-- Evaluate at the same specified vertex, in the original target space. -/
def evaluation (K : SSet.{0}) (W : Space) (v : (Δ[0] : SSet.{0}) ⟶ K) :
    cotensor K W ⟶ W := evaluateVertex K W v ≫ (pointIso W).hom

/-- The exact constant section is a strict section of this evaluation. -/
theorem constantSection_evaluation (K : SSet.{0}) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ K) :
    constantSection K W ≫ evaluation K W v = 𝟙 W := by
  rw [evaluation, ← Category.assoc,
    OrdinarySegalHorizontalCotensorPoint.constantSection_evaluateVertex,
    Iso.inv_hom_id]

/-- The other composite is precomposition by the original map constant
at the same specified parameter vertex. -/
theorem evaluation_constantSection (K : SSet.{0}) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ K) :
    evaluation K W v ≫ constantSection K W =
      pre (SSet.stdSimplex.isTerminalObj₀.from K ≫ v) W := by
  rw [evaluation, constantSection, evaluateVertex]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (OrdinarySegalHorizontalCotensor.pre_comp
    (SSet.stdSimplex.isTerminalObj₀.from K) v W).symm

#print axioms constantSection_evaluation
#print axioms evaluation_constantSection

end
end DaggerModels.PartII.OrdinarySegalCotensorPointEvaluation
