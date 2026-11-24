import DaggerModelsPartII.C2InvolutionOrbits

/-!
# The literal `C₂` action of an involutive endomorphism

The manuscript's involutive discrete diagrams are turned into native actions
of the same lifted two-element group used for the simplicial `EC₂`.
-/

set_option autoImplicit false

open CategoryTheory
open DaggerOriginalDaggerRealizationC2Action

universe u v w

namespace DaggerModels.PartII.C2InvolutionActions

noncomputable section

variable {D : Type v} [Category.{w} D]

/-- The nonidentity group element acts by the given involutive endomorphism. -/
def ofInvolution {X : D} (τ : X ⟶ X) (hτ : τ ≫ τ = 𝟙 X) : Action D C2.{u} where
  V := X
  ρ := {
    toFun g := if g = 1 then 1 else τ
    map_one' := by simp
    map_mul' := by
      intro g h
      rcases C2InvolutionOrbits.c2_cases g with rfl | rfl
      · simp
      rcases C2InvolutionOrbits.c2_cases h with rfl | rfl
      · simp
      have hg : generator.{u} * generator = (1 : C2.{u}) := by decide
      have hne : generator.{u} ≠ (1 : C2.{u}) := by decide
      simp [hg, hne, End.mul_def, hτ] }

@[simp] theorem ofInvolution_generator {X : D} (τ : X ⟶ X) (hτ : τ ≫ τ = 𝟙 X) :
    (ofInvolution.{u} τ hτ).ρ generator = τ := by
  have hne : generator.{u} ≠ (1 : C2.{u}) := by decide
  simp [ofInvolution, hne]

/-- A map commuting with the involutions is equivariant for these actual `C₂` actions. -/
def map {X Y : D} (τ : X ⟶ X) (hτ : τ ≫ τ = 𝟙 X)
    (υ : Y ⟶ Y) (hυ : υ ≫ υ = 𝟙 Y) (f : X ⟶ Y) (hf : τ ≫ f = f ≫ υ) :
    ofInvolution.{u} τ hτ ⟶ ofInvolution.{u} υ hυ where
  hom := f
  comm g := by
    rcases C2InvolutionOrbits.c2_cases g with rfl | rfl
    · simp
    · simpa only [ofInvolution_generator] using hf

variable {C : Type v} [Category.{w} C]

/-- The actual discrete simplicial-set embedding for ordinary set-valued diagrams. -/
def discreteDiagram : (C ⥤ Type u) ⥤ (C ⥤ SSet.{u}) :=
  (Functor.whiskeringRight C (Type u) SSet.{u}).obj (SimplicialObject.const (Type u))

/-- An involutive set-valued diagram gives the native action on its discretization. -/
def discreteAction (X : C ⥤ Type u) (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X) :
    Action (C ⥤ SSet.{u}) C2.{u} :=
  (discreteDiagram.mapAction C2.{u}).obj (ofInvolution τ.hom hτ)

@[simp] theorem discreteAction_generator (X : C ⥤ Type u)
    (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X) :
    (discreteAction X τ hτ).ρ generator = discreteDiagram.map τ.hom := by
  change discreteDiagram.map ((ofInvolution τ.hom hτ).ρ generator) = _
  rw [ofInvolution_generator]

/-- The invariant subdiagram inclusion is equivariant after discretization. -/
def discreteSubsetInclusion (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → DiscreteBorelDiagram.valueEquiv X τ c x ∈ A.obj c) :
    discreteAction A.toFunctor (DiscreteBorelDiagram.subsetAction X τ hτ A hA)
      (DiscreteBorelDiagram.subsetAction_involutive X τ hτ A hA) ⟶
        discreteAction X τ hτ := by
  have hc : (DiscreteBorelDiagram.subsetAction X τ hτ A hA).hom ≫ A.ι =
      A.ι ≫ τ.hom := by
    apply NatTrans.ext
    funext c x
    rfl
  exact (discreteDiagram.mapAction C2.{u}).map
    (map _ (DiscreteBorelDiagram.subsetAction_involutive X τ hτ A hA) _ hτ A.ι hc)

@[simp] theorem discreteSubsetInclusion_hom (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → DiscreteBorelDiagram.valueEquiv X τ c x ∈ A.obj c) :
    (discreteSubsetInclusion X τ hτ A hA).hom = discreteDiagram.map A.ι := rfl

/-- Discretization retains the literal invariant-subset monomorphism. -/
theorem discreteSubsetInclusion_mono (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → DiscreteBorelDiagram.valueEquiv X τ c x ∈ A.obj c) :
    Mono (discreteSubsetInclusion X τ hτ A hA).hom := by
  rw [discreteSubsetInclusion_hom]
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro c
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  exact (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective

end

end DaggerModels.PartII.C2InvolutionActions
