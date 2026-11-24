import DaggerModelsPartII.HomotopyMappingEquivalence
import DaggerModelsPartII.ReedyProperties
import DaggerModelsPartII.ResolutionGenerators

/-! The local objects and local equivalences for the literal resolution family. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localityCoefficientLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localityCoefficientColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localityReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

/-- A Reedy fibrant object local with respect to the given small family of collapse maps. -/
def resolutionLocalObject (W : ResolutionDiagram.{u}) : Prop :=
  IsFibrant W ∧ ∀ ⦃X Y : ResolutionDiagram.{u}⦄ (s : X ⟶ Y),
    resolutionGenerators s → homotopyMappingWeakEquivalences W s

/-- The maps that induce a weak equivalence of homotopy mapping complexes into every
Reedy fibrant local object. -/
def resolutionLocalEquivalences : MorphismProperty ResolutionDiagram.{u} :=
  fun _ _ f ↦ ∀ W : ResolutionDiagram.{u}, resolutionLocalObject W →
    homotopyMappingWeakEquivalences W f

/-- The local-object test spelled out for the free boundaries and simplices in the paper. -/
theorem resolutionLocalObject_iff (W : ResolutionDiagram.{u}) :
    resolutionLocalObject W ↔ IsFibrant W ∧
      ∀ (n : ℕ) (simplex : Bool) (k : ℕ),
        homotopyMappingWeakEquivalences W
          (tensorCollapse (resolutionTestObject n simplex) (k + 1)) := by
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨hw, fun n simplex k ↦ h _ ⟨(n, simplex, k)⟩⟩
  · rintro ⟨hw, h⟩
    refine ⟨hw, ?_⟩
    intro X Y f hf
    obtain ⟨⟨n, simplex, k⟩⟩ := hf
    exact h n simplex k

/-- The collapse maps and all ordinary simplex operators give the same local-object test. -/
theorem resolutionLocalObject_iff_allOperators (W : ResolutionDiagram.{u}) :
    resolutionLocalObject W ↔ IsFibrant W ∧
      ∀ (n : ℕ) (simplex : Bool) (i j : ℕ) (f : ⦋i⦌ ⟶ ⦋j⦌),
        homotopyMappingWeakEquivalences W
          ((externalTensor (resolutionTestObject n simplex)).map (SSet.stdSimplex.map f)) := by
  rw [resolutionLocalObject_iff]
  constructor
  · rintro ⟨hw, h⟩
    letI := hw
    refine ⟨hw, fun n simplex ↦ ?_⟩
    exact (tensorCollapseTests_iff_allOperators (resolutionTestObject n simplex)
      (homotopyMappingWeakEquivalences W)).mp (h n simplex)
  · rintro ⟨hw, h⟩
    letI := hw
    refine ⟨hw, fun n simplex ↦ ?_⟩
    exact (tensorCollapseTests_iff_allOperators (resolutionTestObject n simplex)
      (homotopyMappingWeakEquivalences W)).mpr (h n simplex)

/-- Reedy weak equivalences are resolution-local equivalences. -/
theorem reedyWeakEquivalences_le_resolutionLocalEquivalences :
    reedyWeakEquivalences.{u} ≤ resolutionLocalEquivalences.{u} := by
  intro X Y f hf W hW
  letI := hW.1
  exact weakEquivalences_le_homotopyMappingWeakEquivalences W f hf

/-- Each map of the exact family `S_h` is a resolution-local equivalence. -/
theorem resolutionGenerators_le_localEquivalences :
    resolutionGenerators.{u} ≤ resolutionLocalEquivalences.{u} :=
  fun _ _ f hf _ hW ↦ hW.2 f hf

instance resolutionLocalEquivalences_containsIdentities :
    resolutionLocalEquivalences.{u}.ContainsIdentities where
  id_mem X := reedyWeakEquivalences_le_resolutionLocalEquivalences (𝟙 X)
    ((weakEquivalences ResolutionDiagram.{u}).id_mem X)

instance resolutionLocalEquivalences_hasTwoOutOfThree :
    resolutionLocalEquivalences.{u}.HasTwoOutOfThreeProperty where
  comp_mem f g hf hg W hW := by
    letI := hW.1
    exact (homotopyMappingWeakEquivalences W).comp_mem _ _ (hf W hW) (hg W hW)
  of_precomp f g hf hfg W hW := by
    letI := hW.1
    exact (homotopyMappingWeakEquivalences W).of_precomp _ _ (hf W hW) (hfg W hW)
  of_postcomp f g hg hfg W hW := by
    letI := hW.1
    exact (homotopyMappingWeakEquivalences W).of_postcomp _ _ (hg W hW) (hfg W hW)

instance resolutionLocalEquivalences_isStableUnderRetracts :
    resolutionLocalEquivalences.{u}.IsStableUnderRetracts where
  of_retract r hg W hW := by
    letI := hW.1
    exact MorphismProperty.of_retract (P := homotopyMappingWeakEquivalences W) r (hg W hW)

/-- Locality is invariant under a Reedy weak equivalence between Reedy fibrant diagrams. -/
theorem resolutionLocalObject_iff_of_reedyWeakEquivalence {W V : ResolutionDiagram.{u}}
    [IsFibrant W] [IsFibrant V] (f : W ⟶ V) (hf : reedyWeakEquivalences f) :
    resolutionLocalObject W ↔ resolutionLocalObject V := by
  have hf' : weakEquivalences ResolutionDiagram.{u} f := hf
  constructor
  · intro hW
    refine ⟨inferInstance, ?_⟩
    intro X Y s hs
    have h := homotopyMappingWeakEquivalences_target_iff (C := ResolutionDiagram.{u}) f hf' s
    exact h.mp (hW.2 s hs)
  · intro hV
    refine ⟨inferInstance, ?_⟩
    intro X Y s hs
    have h := homotopyMappingWeakEquivalences_target_iff (C := ResolutionDiagram.{u}) f hf' s
    exact h.mpr (hV.2 s hs)

end

end DaggerModels.PartII
