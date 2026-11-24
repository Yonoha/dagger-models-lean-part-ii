import DaggerModelsPartII.DiscreteBorelOrbitComparison
import DaggerModelsPartII.DiscreteStrictOrbitComparison
import DaggerModelsPartII.BorelLocalTrivialCofibration
import DaggerModelsPartII.DiscreteBorelLocalReduction
import DaggerModelsPartII.SegalLocalizationModels

/-!
# The discrete Borel orbit comparison

An invariant subdiagram containing all fixed elements induces a localized
trivial cofibration on strict orbit diagrams whenever the original discrete
inclusion is a local equivalence. Both the Borel trivial-cofibration input
and the pushout-collapse comparison are proved, rather than assumed.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.DiscreteBorelTheorem

open C2InvolutionActions DiscreteBorelDiagram DiscreteBorelOrbitComparison
open EquivariantDiagramMapping BorelDiscreteOrbits

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- The orbit inclusion for a discrete invariant subdiagram is a localized
trivial cofibration under the manuscript's local-equivalence and fixed-point hypotheses. -/
theorem strictOrbitInclusion_localTrivial
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ k, Mono (s k).hom)
    (X : C ⥤ Type u) (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X)
    (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c)
    (hfixed : ∀ c x, valueEquiv X τ c x = x → x ∈ A.obj c)
    (hlocal : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences (discreteDiagram.map A.ι)) :
    (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations
        (subsetStrictOrbitInclusion X τ hτ A hA) ∧
      (InjectiveKanDiagram.localizedModelCategory
        C I s hs).categoryWithWeakEquivalences.weakEquivalences
          (subsetStrictOrbitInclusion X τ hτ A hA) := by
  let N := InjectiveKanDiagram.localizedModelCategory C I s hs
  let φ := discreteSubsetInclusion X τ hτ A hA
  have hi : N.categoryWithCofibrations.cofibrations φ.hom := by
    rw [(InjectiveKanDiagram.localized_exactClasses C I s hs).1]
    letI : ModelCategory (C ⥤ SSet.{u}) := InjectiveKanDiagram.modelCategory C
    change cofibrations (C ⥤ SSet.{u}) φ.hom
    rw [InjectiveKanDiagram.model_cofibrations]
    haveI : Mono φ.hom := discreteSubsetInclusion_mono X τ hτ A hA
    exact monomorphisms.infer_property _
  have hwi : N.categoryWithWeakEquivalences.weakEquivalences φ.hom := hlocal
  have hnative := actualEC2_orbitTensor_localTrivialCofibration C I s hs φ hi hwi
  let eA := nativeBorelDiagramIso C A.toFunctor (subsetAction X τ hτ A hA)
    (subsetAction_involutive X τ hτ A hA)
  let eX := nativeBorelDiagramIso C X τ hτ
  let e : Arrow.mk (((orbitTensorBifunctor C).map φ).app simplicialAction) ≅
      Arrow.mk (subsetBorelDiagramInclusion X τ hτ simplicialEC2
        ec2Involution ec2Involution_square A hA) :=
    Arrow.isoMk eA eX (nativeBorelDiagramIso_subset_naturality C X τ hτ A hA).symm
  have hborel : N.categoryWithCofibrations.cofibrations
        (subsetBorelDiagramInclusion X τ hτ simplicialEC2
          ec2Involution ec2Involution_square A hA) ∧
      N.categoryWithWeakEquivalences.weakEquivalences
        (subsetBorelDiagramInclusion X τ hτ simplicialEC2
          ec2Involution ec2Involution_square A hA) := by
    letI : ModelCategory (C ⥤ SSet.{u}) := N
    exact ⟨((cofibrations (C ⥤ SSet.{u})).arrow_mk_iso_iff e).mp hnative.1,
      ((weakEquivalences (C ⥤ SSet.{u})).arrow_mk_iso_iff e).mp hnative.2⟩
  apply strictOrbitInclusion_localTrivial_of_borel X τ hτ simplicialEC2
    ec2Involution ec2Involution_square A hA I s hs hfixed _ hborel.1 hborel.2
  haveI : Nonempty C2.{u} := ⟨1⟩
  exact DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration
    (terminal.from simplicialEC2) terminalIsTerminal

/-- The same comparison for the native categorical strict-orbit functor,
with the explicit orbit presentation removed from the conclusion. -/
theorem nativeStrictOrbitInclusion_localTrivial
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ k, Mono (s k).hom)
    (X : C ⥤ Type u) (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X)
    (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c)
    (hfixed : ∀ c x, valueEquiv X τ c x = x → x ∈ A.obj c)
    (hlocal : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences (discreteDiagram.map A.ι)) :
    (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations
        ((ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
          (discreteSubsetInclusion X τ hτ A hA)) ∧
      (InjectiveKanDiagram.localizedModelCategory
        C I s hs).categoryWithWeakEquivalences.weakEquivalences
          ((ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
            (discreteSubsetInclusion X τ hτ A hA)) := by
  have h := strictOrbitInclusion_localTrivial C I s hs X τ hτ A hA hfixed hlocal
  letI : ModelCategory (C ⥤ SSet.{u}) := InjectiveKanDiagram.localizedModelCategory C I s hs
  let e : Arrow.mk ((ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
      (discreteSubsetInclusion X τ hτ A hA)) ≅
      Arrow.mk (subsetStrictOrbitInclusion X τ hτ A hA) := Arrow.isoMk
    (DiscreteStrictOrbitComparison.nativeDiscreteStrictOrbitIso C A.toFunctor
      (subsetAction X τ hτ A hA) (subsetAction_involutive X τ hτ A hA))
    (DiscreteStrictOrbitComparison.nativeDiscreteStrictOrbitIso C X τ hτ)
    (DiscreteStrictOrbitComparison.nativeDiscreteStrictOrbitIso_subset_naturality
      C X τ hτ A hA).symm
  exact ⟨((cofibrations (C ⥤ SSet.{u})).arrow_mk_iso_iff e).mpr h.1,
    ((weakEquivalences (C ⥤ SSet.{u})).arrow_mk_iso_iff e).mpr h.2⟩

/-- The manuscript's Borel orbit comparison for the actual reversal Segal localization. -/
theorem reversal_strictOrbitInclusion_localTrivial
    (X : DaggerModels.ReverseSimplexᵒᵖ ⥤ Type)
    (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X) (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c)
    (hfixed : ∀ c x, valueEquiv X τ c x = x → x ∈ A.obj c)
    (hlocal : SegalLocalizers.injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences (discreteDiagram.map A.ι)) :
    SegalLocalizers.injectiveSegalModel.categoryWithCofibrations.cofibrations
        (subsetStrictOrbitInclusion X τ hτ A hA) ∧
      SegalLocalizers.injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (subsetStrictOrbitInclusion X τ hτ A hA) :=
  strictOrbitInclusion_localTrivial DaggerModels.ReverseSimplexᵒᵖ
    SegalLocalizers.LocalizerIndex SegalLocalizers.localizerArrow
    SegalLocalizers.localizerArrow_mono X τ hτ A hA hfixed hlocal

end

end DaggerModels.PartII.DiscreteBorelTheorem
