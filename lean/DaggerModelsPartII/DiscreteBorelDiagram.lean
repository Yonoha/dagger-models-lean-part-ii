import DaggerModelsPartII.BorelPushoutCollapse
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Discrete Borel constructions on diagrams of involutive sets

The strict orbit and Borel constructions are formed objectwise from the actual
involution on the input diagram. Their maps retain the specified action on every
arrow of the index category.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u v w

namespace DaggerModels.PartII.DiscreteBorelDiagram

open DaggerModels.FreeInvolution DaggerModels.PartII.DiagonalInvolutionOrbits
  DaggerModels.PartII.BorelDiscreteOrbits DaggerModels.PartII.DiscreteOrbitSubobject

noncomputable section

variable {C : Type v} [Category.{w} C] (X : C ⥤ Type u)
  (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X)

/-- The action on one value of a diagram. -/
def valueEquiv (c : C) : X.obj c ≃ X.obj c := (τ.app c).toEquiv

include hτ in
theorem valueInvolutive (c : C) : Function.Involutive (valueEquiv X τ c) := by
  intro x
  exact congrFun (congr_app hτ c) x

theorem value_comm {c d : C} (f : c ⟶ d) (x : X.obj c) :
    X.map f (valueEquiv X τ c x) = valueEquiv X τ d (X.map f x) :=
  (congrFun (τ.hom.naturality f) x).symm

/-- An equivariant map on first factors induces a map on diagonal orbits. -/
def firstMap {U V : Type u} (α : U ≃ U) (hα : Function.Involutive α)
    (β : V ≃ V) (hβ : Function.Involutive β)
    {Y : Type u} (σ : Y ≃ Y) (hσ : Function.Involutive σ)
    (f : U → V) (hf : ∀ x, f (α x) = β (f x)) :
    DiagonalOrbit α hα σ hσ → DiagonalOrbit β hβ σ hσ :=
  Quotient.map' (fun p : U × Y ↦ (f p.1, p.2)) (by
    intro p q hpq
    rcases hpq with h | h
    · exact Or.inl (congrArg (fun p : U × Y ↦ (f p.1, p.2)) h)
    · apply Or.inr
      change (f p.1, p.2) = (β (f q.1), σ q.2)
      exact Prod.ext ((congrArg (fun p : U × Y ↦ f p.1) h).trans (hf q.1))
        (congrArg (fun p : U × Y ↦ p.2) h))

/-- An equivariant map induces a map on strict orbit sets. -/
def strictOrbitMap {U V : Type u} (α : U ≃ U) (hα : Function.Involutive α)
    (β : V ≃ V) (hβ : Function.Involutive β)
    (f : U → V) (hf : ∀ x, f (α x) = β (f x)) :
    Orbit α hα → Orbit β hβ :=
  Quotient.map' f (by
    intro x y hxy
    rcases hxy with h | h
    · exact Or.inl (congrArg f h)
    · exact Or.inr ((congrArg f h).trans (hf y)))

/-- Strict orbit sets, as a diagram of constant simplicial sets. -/
def strictOrbitDiagram : C ⥤ SSet.{u} where
  obj c := (SimplicialObject.const (Type u)).obj
    (Orbit (valueEquiv X τ c) (valueInvolutive X τ hτ c))
  map {c d} f := (SimplicialObject.const (Type u)).map
    (strictOrbitMap (valueEquiv X τ c) (valueInvolutive X τ hτ c)
      (valueEquiv X τ d) (valueInvolutive X τ hτ d)
      (X.map f) (value_comm X τ f))
  map_id c := by
    apply NatTrans.ext
    funext n q
    induction q using Quotient.inductionOn with
    | _ x =>
      change orbit _ _ (X.map (𝟙 c) x) = orbit _ _ x
      rw [X.map_id]
      rfl
  map_comp {a b c} f g := by
    apply NatTrans.ext
    funext n q
    induction q using Quotient.inductionOn with
    | _ x =>
      change orbit _ _ (X.map (f ≫ g) x) = orbit _ _ (X.map g (X.map f x))
      rw [X.map_comp]
      rfl

variable (E : SSet.{u}) (σ : E ≅ E) (hσ : σ.hom ≫ σ.hom = 𝟙 E)

/-- The objectwise discrete Borel construction forms a simplicial-set-valued diagram. -/
def borelDiagram : C ⥤ SSet.{u} where
  obj c := borel E σ hσ (valueEquiv X τ c) (valueInvolutive X τ hτ c)
  map {c d} f := {
    app n := firstMap (valueEquiv X τ c) (valueInvolutive X τ hτ c)
      (valueEquiv X τ d) (valueInvolutive X τ hτ d)
      (degreeEquiv E σ n) (degree_involutive E σ hσ n)
      (X.map f) (value_comm X τ f)
    naturality n m α := by
      funext q
      induction q using Quotient.inductionOn with
      | _ p => rfl }
  map_id c := by
    apply NatTrans.ext
    funext n q
    induction q using Quotient.inductionOn with
    | _ p =>
      change orbit _ _ (X.map (𝟙 c) p.1, p.2) = orbit _ _ p
      rw [X.map_id]
      rfl
  map_comp {a b c} f g := by
    apply NatTrans.ext
    funext n q
    induction q using Quotient.inductionOn with
    | _ p =>
      change orbit _ _ (X.map (f ≫ g) p.1, p.2) =
        orbit _ _ (X.map g (X.map f p.1), p.2)
      rw [X.map_comp]
      rfl

/-- The Borel collapse is natural in the external diagram index. -/
def diagramCollapse : borelDiagram X τ hτ E σ hσ ⟶ strictOrbitDiagram X τ hτ where
  app c := collapse E σ hσ (valueEquiv X τ c) (valueInvolutive X τ hτ c)
  naturality c d f := by
    apply NatTrans.ext
    funext n q
    induction q using Quotient.inductionOn with
    | _ p => rfl

variable (A : Subfunctor X)
  (hA : ∀ (c : C) (x : X.obj c), x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c)

/-- Restriction of the diagram involution to an invariant subfunctor. -/
def subsetAction : A.toFunctor ≅ A.toFunctor :=
  NatIso.ofComponents (fun c ↦ Equiv.toIso
    (restrictedInvolution (valueEquiv X τ c) (valueInvolutive X τ hτ c)
      (A.obj c) (hA c))) (by
    intro c d f
    funext x
    apply Subtype.ext
    exact (value_comm X τ f x.1).symm)

theorem subsetAction_involutive :
    (subsetAction X τ hτ A hA).hom ≫ (subsetAction X τ hτ A hA).hom =
      𝟙 A.toFunctor := by
  apply NatTrans.ext
  funext c x
  apply Subtype.ext
  exact valueInvolutive X τ hτ c x.1

/-- The subset action is literally the restricted action at every value. -/
theorem subsetAction_value (c : C) (x : A.toFunctor.obj c) :
    valueEquiv A.toFunctor (subsetAction X τ hτ A hA) c x =
      restrictedInvolution (valueEquiv X τ c) (valueInvolutive X τ hτ c)
        (A.obj c) (hA c) x := rfl

/-- Inclusion of the subset's strict orbit diagram into the ambient one. -/
def subsetStrictOrbitInclusion :
    strictOrbitDiagram A.toFunctor (subsetAction X τ hτ A hA)
      (subsetAction_involutive X τ hτ A hA) ⟶
        strictOrbitDiagram X τ hτ where
  app c := (SimplicialObject.const (Type u)).map
    (orbitInclusion (valueEquiv X τ c) (valueInvolutive X τ hτ c)
      (A.obj c) (hA c))
  naturality c d f := by
    apply NatTrans.ext
    funext n q
    induction q using Quotient.inductionOn with
    | _ x => rfl

/-- Inclusion of the subset's Borel diagram into the ambient Borel diagram. -/
def subsetBorelDiagramInclusion :
    borelDiagram A.toFunctor (subsetAction X τ hτ A hA)
      (subsetAction_involutive X τ hτ A hA) E σ hσ ⟶
        borelDiagram X τ hτ E σ hσ where
  app c := subsetBorelInclusion E σ hσ (valueEquiv X τ c)
    (valueInvolutive X τ hτ c) (A.obj c) (hA c)
  naturality c d f := by
    apply NatTrans.ext
    funext n q
    induction q using Quotient.inductionOn with
    | _ p => rfl

@[reassoc (attr := simp)] theorem subsetBorelDiagramInclusion_collapse :
    subsetBorelDiagramInclusion X τ hτ E σ hσ A hA ≫
      diagramCollapse X τ hτ E σ hσ =
        diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
          (subsetAction_involutive X τ hτ A hA) E σ hσ ≫
            subsetStrictOrbitInclusion X τ hτ A hA := by
  apply NatTrans.ext
  funext c
  exact subsetInclusion_collapse E σ hσ (valueEquiv X τ c)
    (valueInvolutive X τ hτ c) (A.obj c) (hA c)

/-- The canonical pushout after collapsing the invariant subset. -/
def collapsedDiagramPushout : C ⥤ SSet.{u} :=
  pushout (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA)
    (diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
      (subsetAction_involutive X τ hτ A hA) E σ hσ)

/-- The canonical collapse from the diagram pushout to the strict orbit diagram. -/
def diagramPushoutCollapse : collapsedDiagramPushout X τ hτ E σ hσ A hA ⟶
    strictOrbitDiagram X τ hτ :=
  pushout.desc (diagramCollapse X τ hτ E σ hσ)
    (subsetStrictOrbitInclusion X τ hτ A hA)
    (subsetBorelDiagramInclusion_collapse X τ hτ E σ hσ A hA)

/-- Evaluation sends the diagram pushout to the ordinary simplicial pushout. -/
def evaluatedPushout (c : C) : IsPushout
    ((subsetBorelDiagramInclusion X τ hτ E σ hσ A hA).app c)
    ((diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
      (subsetAction_involutive X τ hτ A hA) E σ hσ).app c)
    ((pushout.inl
      (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA)
      (diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) E σ hσ)).app c)
    ((pushout.inr
      (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA)
      (diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) E σ hσ)).app c) := by
  convert IsPushout.map ((evaluation C SSet.{u}).obj c)
    (IsPushout.of_hasPushout
      (subsetBorelDiagramInclusion X τ hτ E σ hσ A hA)
      (diagramCollapse A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) E σ hσ)) using 1

/-- The evaluated pushout is canonically isomorphic to the pointwise one. -/
def evaluatedPushoutIso (c : C) :
    (collapsedDiagramPushout X τ hτ E σ hσ A hA).obj c ≅
      collapsedPushout E σ hσ (valueEquiv X τ c)
        (valueInvolutive X τ hτ c) (A.obj c) (hA c) :=
  (evaluatedPushout X τ hτ E σ hσ A hA c).isoPushout

/-- Evaluation of the diagram collapse is the pointwise canonical collapse. -/
theorem evaluatedCollapse_factor (c : C) :
    (diagramPushoutCollapse X τ hτ E σ hσ A hA).app c =
      (evaluatedPushoutIso X τ hτ E σ hσ A hA c).hom ≫
        pushoutCollapse E σ hσ (valueEquiv X τ c)
          (valueInvolutive X τ hτ c) (A.obj c) (hA c) := by
  apply (evaluatedPushout X τ hτ E σ hσ A hA c).hom_ext
  · calc
      _ = (diagramCollapse X τ hτ E σ hσ).app c := by
        change (pushout.inl _ _ ≫ diagramPushoutCollapse X τ hτ E σ hσ A hA).app c = _
        simp [diagramPushoutCollapse]
      _ = _ := by
        dsimp only [evaluatedPushoutIso]
        rw [← Category.assoc,
          (evaluatedPushout X τ hτ E σ hσ A hA c).inl_isoPushout_hom]
        change collapse E σ hσ (valueEquiv X τ c) (valueInvolutive X τ hτ c) =
          pushout.inl _ _ ≫ pushoutCollapse E σ hσ (valueEquiv X τ c)
            (valueInvolutive X τ hτ c) (A.obj c) (hA c)
        simp [pushoutCollapse]

  · calc
      _ = (subsetStrictOrbitInclusion X τ hτ A hA).app c := by
        change (pushout.inr _ _ ≫ diagramPushoutCollapse X τ hτ E σ hσ A hA).app c = _
        simp [diagramPushoutCollapse]
      _ = _ := by
        dsimp only [evaluatedPushoutIso]
        rw [← Category.assoc,
          (evaluatedPushout X τ hτ E σ hσ A hA c).inr_isoPushout_hom]
        change InvariantOrbitSets.subsetConstantInclusion (valueEquiv X τ c)
            (valueInvolutive X τ hτ c) (A.obj c) (hA c) =
          pushout.inr _ _ ≫ pushoutCollapse E σ hσ (valueEquiv X τ c)
            (valueInvolutive X τ hτ c) (A.obj c) (hA c)
        simp [pushoutCollapse]

/-- The canonical diagram pushout collapse is an ordinary Kan weak equivalence
at every index object, provided each fixed element belongs to the subset. -/
theorem diagramPushoutCollapse_pointwiseWeak
    (hfixed : ∀ (c : C) (x : X.obj c), valueEquiv X τ c x = x → x ∈ A.obj c)
    (hE : trivialFibrations SSet.{u} (terminal.from E)) (c : C) :
    weakEquivalences SSet.{u}
      ((diagramPushoutCollapse X τ hτ E σ hσ A hA).app c) := by
  rw [evaluatedCollapse_factor]
  haveI : WeakEquivalence
      (pushoutCollapse E σ hσ (valueEquiv X τ c) (valueInvolutive X τ hτ c)
        (A.obj c) (hA c)) :=
    (weakEquivalence_iff _).mpr
      (pushoutCollapse_weak E σ hσ (valueEquiv X τ c) (valueInvolutive X τ hτ c)
        (A.obj c) (hA c) (hfixed c) hE)
  exact (weakEquivalence_iff _).mp inferInstance

/-- The diagram Borel construction using the manuscript's actual simplicial `EC₂`. -/
abbrev actualBorelDiagram : C ⥤ SSet.{u} :=
  borelDiagram X τ hτ DaggerOriginalEC2SimplicialAction.simplicialEC2
    ec2Involution ec2Involution_square

/-- The actual `EC₂` pushout collapse is a weak equivalence at each index. -/
theorem actualEC2_diagramPushoutCollapse_pointwiseWeak
    (hfixed : ∀ (c : C) (x : X.obj c), valueEquiv X τ c x = x → x ∈ A.obj c)
    (c : C) :
    weakEquivalences SSet.{u}
      ((diagramPushoutCollapse X τ hτ
        DaggerOriginalEC2SimplicialAction.simplicialEC2
        ec2Involution ec2Involution_square A hA).app c) := by
  apply diagramPushoutCollapse_pointwiseWeak X τ hτ
    DaggerOriginalEC2SimplicialAction.simplicialEC2
    ec2Involution ec2Involution_square A hA hfixed
  haveI : Nonempty DaggerOriginalDaggerRealizationC2Action.C2.{u} := ⟨1⟩
  exact DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration
    (terminal.from DaggerOriginalEC2SimplicialAction.simplicialEC2) terminalIsTerminal

end

end DaggerModels.PartII.DiscreteBorelDiagram
