import DaggerModelsPartII.ReedyModelComparison
import DaggerModelsPartII.ResolutionGenerators
import DaggerModels.FreeDaggerCofibration
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-! The two endpoints of each resolution localization map are Reedy cofibrant. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance : ModelCategory DaggerSSet.{u} := DaggerOriginalJoyalModel.standardModelCategory
local instance : ModelCategory ResolutionDiagram.{u} := resolutionReedyModelCategory

/-- Each free dagger simplicial set is cofibrant in the coefficient model. -/
theorem freeDagger_isCofibrant (K : SSet.{u}) : IsCofibrant (freeDagger.obj K) := by
  letI := freeDaggerAdjunction.leftAdjoint_preservesColimits
  apply (isCofibrant_iff_of_isInitial (freeDagger.map (initial.to K))
    (initialIsInitial.isInitialObj freeDagger _)).mpr
  apply (cofibration_iff _).mpr
  change DaggerOriginalJoyalModel.standardModelCategory.categoryWithCofibrations.cofibrations _
  rw [DaggerOriginalJoyalModel.standard_model_cof]
  exact freeDagger_map_isFreeCofibration _

/-- The tensors of the specified test objects with simplices are Reedy cofibrant. -/
theorem resolutionTestTensor_isCofibrant (n : ℕ) (simplex : Bool) (k : ℕ) :
    IsCofibrant ((externalTensor (resolutionTestObject.{u} n simplex)).obj Δ[k]) := by
  let F := externalTensorWith (Δ[k] : SSet.{u})
  let A := resolutionTestObject.{u} n simplex
  change IsCofibrant (F.obj A)
  letI : PreservesColimits F := (evaluationAdjunction k).leftAdjoint_preservesColimits
  letI : F.PreservesCofibrations := (evaluationAdjunction_isQuillen k).toPreservesCofibrations
  letI : IsCofibrant A := freeDagger_isCofibrant _
  apply (isCofibrant_iff_of_isInitial (F.map (initial.to A))
    (initialIsInitial.isInitialObj F _)).mpr
  infer_instance

/-- Every arrow of the manuscript's family `S_h` has Reedy cofibrant endpoints. -/
theorem resolutionGenerator_cofibrantEndpoints {X Y : ResolutionDiagram.{u}}
    (f : X ⟶ Y) (hf : resolutionGenerators f) : IsCofibrant X ∧ IsCofibrant Y := by
  obtain ⟨⟨n, simplex, k⟩⟩ := hf
  exact ⟨resolutionTestTensor_isCofibrant n simplex (k + 1),
    resolutionTestTensor_isCofibrant n simplex 0⟩

end

end DaggerModels.PartII
