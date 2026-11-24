import OrdinarySegalCotensorPointEvaluation

/-!
# Evaluation commutes strictly with parameter restriction

The point evaluation uses the original vertex followed by the checked
point-parameter isomorphism. Contravariant composition therefore gives
an equality of whole maps of ordinary simplicial spaces.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCotensorEvaluationNaturality

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalCotensorPointEvaluation (evaluation)

noncomputable section

/-- Restricting a parameter and then evaluating at its original vertex
is evaluation at the image of that same vertex. -/
theorem evaluation_pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ K) :
    pre f W ≫ evaluation K W v = evaluation L W (v ≫ f) := by
  change (pre f W ≫ pre v W) ≫
      (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom =
    pre (v ≫ f) W ≫
      (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom
  rw [OrdinarySegalHorizontalCotensor.pre_comp]

#print axioms evaluation_pre

end
end DaggerModels.PartII.OrdinarySegalCotensorEvaluationNaturality
