import OrdinaryWalkingAlternatingExhaustion
import DaggerModelsPartII.JTSimplexUnitKan

/-!
# The original directed edge is isomorphic to the literal initial stage

The original simplex unit is already known to be monomorphic. The pinned
image factorization therefore identifies its unchanged domain with its
actual image, which is precisely the checked first alternating stage.
Both inclusion equations retain the original simplex unit.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingInitialStageIso

open OrdinaryWalkingAlternatingFiltration OrdinaryWalkingAlternatingExhaustion

noncomputable section

/-- The actual original directed one-simplex is the first literal stage. -/
def initialStageIso : (Δ[1] : SSet.{0}) ≅ (stage 1 : SSet.{0}) := by
  have : Mono (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) :=
    JTSimplexUnitKan.simplexUnit_mono ⦋1⦌
  exact asIso (SSet.Subcomplex.toRange (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)) ≪≫
    SSet.Subcomplex.eqToIso stage_one_eq_unit_image.symm

/-- Its composite into the original walking parameter is the original unit. -/
theorem initialStageIso_hom_ι : initialStageIso.hom ≫ (stage 1).ι =
    JTCylinderCEComparison.simplexUnit.app ⦋1⦌ := by
  change (SSet.Subcomplex.toRange (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) ≫
    SSet.Subcomplex.homOfLE stage_one_eq_unit_image.symm.le) ≫ (stage 1).ι = _
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι]

/-- The inverse retains the same inclusion into the whole walking parameter. -/
theorem initialStageIso_inv_unit : initialStageIso.inv ≫
    JTCylinderCEComparison.simplexUnit.app ⦋1⦌ = (stage 1).ι := by
  rw [← initialStageIso_hom_ι, ← Category.assoc, initialStageIso.inv_hom_id,
    Category.id_comp]

#print axioms initialStageIso
#print axioms initialStageIso_hom_ι
#print axioms initialStageIso_inv_unit

end

end DaggerModels.PartII.OrdinaryWalkingInitialStageIso
