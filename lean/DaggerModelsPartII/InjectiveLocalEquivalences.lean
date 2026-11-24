import DaggerModelsPartII.DiagramMappingPrecompFibration
import DaggerModelsPartII.DiagramMappingTransfinite
import DaggerModelsPartII.LocalEquivalencePushouts

/-!
# Closure of injective cofibrations that are local equivalences

Strict mapping spaces carry a continuous colimit to an inverse limit. Since
monomorphisms induce mapping-space fibrations, a transfinite composition of
local trivial cofibrations passes the strict and hence derived local test.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

local instance localWeakInjectiveModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- A local trivial cofibration induces a trivial Kan fibration into any local target. -/
theorem localTrivialCofibration_mapping_trivialFibration
    (S : MorphismProperty (C ⥤ SSet.{u})) {A B : C ⥤ SSet.{u}} (f : A ⟶ B)
    (hf : (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
      Localization.localEquivalences S) f)
    (W : C ⥤ SSet.{u}) (hW : Localization.localObject S W) :
    HomotopicalAlgebra.trivialFibrations SSet.{u} (diagramMappingPrecomp f W) := by
  letI := hW.1
  haveI : Mono f := by
    have h := hf.1
    rw [model_cofibrations C] at h
    exact h
  exact ⟨(fibration_iff _).mp (diagramMappingPrecomp_isFibration C f W),
    (model_homotopyMapping_iff_strict C f).mp (hf.2 W hW)⟩

/-- Injective cofibrations that are local equivalences are stable under pushout. -/
theorem localTrivialCofibrations_cobaseChange (S : MorphismProperty (C ⥤ SSet.{u})) :
    (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
      Localization.localEquivalences S).IsStableUnderCobaseChange := by
  letI : HasColimitsOfSize.{0, u} (C ⥤ SSet.{u}) := hasColimitsOfSizeShrink.{0, u} _
  exact Localization.localTrivialCofibrations_cobaseChange
    (fun sq hi hw ↦ model_leftProper C sq hi hw) S

/-- Injective cofibrations that are local equivalences are stable under transfinite composition. -/
theorem localTrivialCofibrations_transfinite (S : MorphismProperty (C ⥤ SSet.{u})) :
    IsStableUnderTransfiniteComposition.{u}
      (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
        Localization.localEquivalences S) := by
  letI : IsStableUnderTransfiniteComposition.{u}
      (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u})) := by
    rw [← llp_eq_of_wfs (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}))
      (HomotopicalAlgebra.trivialFibrations (C ⥤ SSet.{u}))]
    infer_instance
  constructor
  intro J _ _ _ _
  constructor
  intro A B f hf
  refine ⟨(HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u})).transfiniteCompositionsOfShape_le J _
    (transfiniteCompositionsOfShape_monotone J inf_le_left _ hf), ?_⟩
  obtain ⟨c⟩ := hf
  letI := c.isWellOrderContinuous
  intro W hW
  letI := hW.1
  have ht := diagramMappingPrecomp_colimit_trivialFibration c.F c.isColimit W
    (fun j hj ↦ localTrivialCofibration_mapping_trivialFibration C S _ (c.map_mem j hj) W hW)
  have hh := (model_homotopyMapping_iff_strict C (c.incl.app ⊥)).mpr ht.2
  rw [← c.fac]
  exact (homotopyMappingWeakEquivalences W).comp_mem _ _
    (weakEquivalences_le_homotopyMappingWeakEquivalences W _
      ((HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u})).of_isIso _)) hh

end

end DaggerModels.PartII.InjectiveKanDiagram
