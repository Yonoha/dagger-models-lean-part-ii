import DaggerModelsPartII.ResolutionLocalEvaluation
import DaggerModelsPartII.ResolutionFibrantReplacement

/-! Evaluation of weak equivalences on homotopically constant resolution diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance comparisonCriterionLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance comparisonCriterionColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance comparisonCriterionCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance comparisonCriterionReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

/-- For homotopically constant diagrams a map is Reedy weak exactly when its degree zero is weak. -/
theorem reedyWeakEquivalence_iff_evalZero_of_homotopicallyConstant
    {W V : ResolutionDiagram.{u}} (f : W ⟶ V)
    (hW : reedyWeakEquivalences (resolutionCounit W))
    (hV : reedyWeakEquivalences (resolutionCounit V)) :
    reedyWeakEquivalences f ↔ weakEquivalences DaggerSSet.{u} (f.app (op ⦋0⦌)) := by
  constructor
  · exact fun h ↦ h _
  · intro h k
    have hc : (resolutionCounit W).app k ≫ f.app k =
        f.app (op ⦋0⦌) ≫ (resolutionCounit V).app k :=
      f.naturality (simplexCollapse k).op
    exact (weakEquivalences DaggerSSet.{u}).of_precomp
      ((resolutionCounit W).app k) (f.app k) (hW k)
      (hc.symm ▸ (weakEquivalences DaggerSSet.{u}).comp_mem _ _ h (hV k))

/-- The original constant--evaluation adjunction compares weak maps to homotopically
constant targets before localization. -/
theorem constantEvaluation_reedyWeak_iff {A : DaggerSSet.{u}} {W : ResolutionDiagram.{u}}
    (f : constantDiagram.obj A ⟶ W) (hW : reedyWeakEquivalences (resolutionCounit W)) :
    reedyWeakEquivalences f ↔
      weakEquivalences DaggerSSet.{u} (constantEvaluationAdjunction.homEquiv A W f) := by
  have hA : reedyWeakEquivalences (resolutionCounit (constantDiagram.obj A)) :=
    fun _ ↦ (weakEquivalences DaggerSSet.{u}).id_mem A
  rw [reedyWeakEquivalence_iff_evalZero_of_homotopicallyConstant f hA hW]
  rw [Adjunction.homEquiv_unit]
  change weakEquivalences DaggerSSet.{u} (f.app (op ⦋0⦌)) ↔
    weakEquivalences DaggerSSet.{u} (𝟙 A ≫ f.app (op ⦋0⦌))
  rw [Category.id_comp]

/-- A Reedy fibrant replacement of a constant diagram is local for the exact collapse family. -/
theorem resolutionReedyFibrantReplacement_constant_local (A : DaggerSSet.{u}) :
    resolutionLocalObject (resolutionReedyFibrantReplacement.obj (constantDiagram.obj A)) := by
  letI := resolutionReedyFibrantReplacement_isFibrant (constantDiagram.obj A)
  exact resolutionLocalObject_of_homotopicallyConstant _
    (resolutionReedyFibrantReplacement_constant_counit_weak A)

end

end DaggerModels.PartII
