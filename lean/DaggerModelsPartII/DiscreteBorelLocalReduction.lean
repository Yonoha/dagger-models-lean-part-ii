import DaggerModelsPartII.DiscreteBorelDiagram
import DaggerModelsPartII.InjectiveLocalizationModel

/-!
# The final local step of the discrete Borel comparison

The pointwise collapse is proved independently. Thus a local trivial
cofibration on the Borel constructions implies a local trivial cofibration
on strict orbits. Establishing that Borel hypothesis is a separate theorem.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.DiscreteBorelDiagram

noncomputable section

variable {C : Type u} [Category.{u} C] (X : C ⥤ Type u)
  (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X)
  (E : SSet.{u}) (σ : E ≅ E) (hσ : σ.hom ≫ σ.hom = 𝟙 E)
  (A : Subfunctor X)
  (hA : ∀ (c : C) (x : X.obj c), x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c)

/-- Strict orbit inclusion remains monic for an invariant subdiagram. -/
theorem subsetStrictOrbitInclusion_mono : Mono (subsetStrictOrbitInclusion X τ hτ A hA) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro c
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  apply (CategoryTheory.mono_iff_injective _).mpr
  exact DiscreteOrbitSubobject.orbitInclusion_injective
    (valueEquiv X τ c) (valueInvolutive X τ hτ c) (A.obj c) (hA c)

/-- The final pushout argument for strict orbits, conditional precisely on
the local trivial-cofibration assertion for the Borel inclusion. -/
theorem strictOrbitInclusion_localTrivial_of_borel
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ k, Mono (s k).hom)
    (hfixed : ∀ (c : C) (x : X.obj c), valueEquiv X τ c x = x → x ∈ A.obj c)
    (hE : trivialFibrations SSet.{u} (terminal.from E))
    (hBc : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA))
    (hBw : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences
        (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA)) :
    (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations (subsetStrictOrbitInclusion X τ hτ A hA) ∧
      (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences
          (subsetStrictOrbitInclusion X τ hτ A hA) := by
  let N := InjectiveKanDiagram.localizedModelCategory C I s hs
  have he := InjectiveKanDiagram.localized_exactClasses C I s hs
  have hcof : N.categoryWithCofibrations.cofibrations
      (subsetStrictOrbitInclusion X τ hτ A hA) := by
    rw [he.1]
    letI : ModelCategory (C ⥤ SSet.{u}) := InjectiveKanDiagram.modelCategory C
    change cofibrations (C ⥤ SSet.{u}) _
    rw [InjectiveKanDiagram.model_cofibrations]
    haveI := subsetStrictOrbitInclusion_mono X τ hτ A hA
    exact monomorphisms.infer_property _
  have hcollapse : N.categoryWithWeakEquivalences.weakEquivalences
      (diagramPushoutCollapse X τ hτ E σ hσ A hA) := by
    rw [he.2]
    letI : ModelCategory (C ⥤ SSet.{u}) := InjectiveKanDiagram.modelCategory C
    apply Localization.weakEquivalences_le_localEquivalences
      (InjectiveKanDiagram.diagramLocalizingFamily C I s)
    rw [InjectiveKanDiagram.model_weakEquivalences]
    exact diagramPushoutCollapse_pointwiseWeak X τ hτ E σ hσ A hA hfixed hE
  letI : ModelCategory (C ⥤ SSet.{u}) := N
  have hB : trivialCofibrations (C ⥤ SSet.{u})
      (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA) := ⟨hBc, hBw⟩
  have hpush : trivialCofibrations (C ⥤ SSet.{u}) (pushout.inr
      (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA)
      (diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) E σ hσ)) :=
    MorphismProperty.of_isPushout (IsPushout.of_hasPushout _ _).flip hB
  haveI : WeakEquivalence (diagramPushoutCollapse X τ hτ E σ hσ A hA) :=
    (weakEquivalence_iff _).mpr hcollapse
  haveI : WeakEquivalence (pushout.inr
      (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA)
      (diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) E σ hσ)) :=
    (weakEquivalence_iff _).mpr hpush.2
  refine ⟨hcof, ?_⟩
  change weakEquivalences (C ⥤ SSet.{u}) _
  have hfac : pushout.inr _ _ ≫ diagramPushoutCollapse X τ hτ E σ hσ A hA =
      subsetStrictOrbitInclusion X τ hτ A hA := by simp [diagramPushoutCollapse]
  rw [← hfac]
  exact (weakEquivalence_iff _).mp inferInstance

end

end DaggerModels.PartII.DiscreteBorelDiagram
