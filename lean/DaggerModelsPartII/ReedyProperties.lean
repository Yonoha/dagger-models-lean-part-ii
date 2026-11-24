import DaggerModelsPartII.ReedyFibrantDiagrams
import OriginalActualDaggerModelConstruction
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Reedy morphism classes for the actual dagger Joyal coefficients

These are the three classes of `cs.lem.reedy`. The coefficient model is the
one constructed in Part I. Identifying the relative trivial classes with
the intersections with levelwise weak equivalences gives the Reedy
model structure as an explicit value.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Opposite Simplicial HomotopicalAlgebra

universe u

namespace DaggerModels.PartII

noncomputable section

local instance : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance : ModelCategory DaggerSSet.{u} := DaggerOriginalJoyalModel.standardModelCategory

/-- Weak equivalences in the outer simplicial direction are levelwise dagger Joyal ones. -/
def reedyWeakEquivalences : MorphismProperty ResolutionDiagram.{u} :=
  (weakEquivalences DaggerSSet.{u}).functorCategory SimplexCategoryᵒᵖ

/-- A Reedy fibration has dagger Joyal fibration relative matching maps in every degree. -/
def reedyFibrations : MorphismProperty ResolutionDiagram.{u} :=
  reedyMatchingProperty (fibrations DaggerSSet.{u})

/-- A Reedy cofibration has dagger Joyal cofibration relative latching maps in every degree. -/
def reedyCofibrations : MorphismProperty ResolutionDiagram.{u} :=
  reedyLatchingProperty (cofibrations DaggerSSet.{u})

instance reedyWeakEquivalences_hasTwoOutOfThree :
    reedyWeakEquivalences.{u}.HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := fun n ↦ (weakEquivalences DaggerSSet.{u}).comp_mem
    (f.app n) (g.app n) (hf n) (hg n)
  of_precomp f g hf hfg := fun n ↦ (weakEquivalences DaggerSSet.{u}).of_precomp
    (f.app n) (g.app n) (hf n) (hfg n)
  of_postcomp f g hg hfg := fun n ↦ (weakEquivalences DaggerSSet.{u}).of_postcomp
    (f.app n) (g.app n) (hg n) (hfg n)

instance reedyWeakEquivalences_isStableUnderRetracts :
    reedyWeakEquivalences.{u}.IsStableUnderRetracts := by
  unfold reedyWeakEquivalences
  infer_instance

/-- Evaluation at zero carries a Reedy fibration to a dagger Joyal fibration. -/
theorem reedyFibration_evalZero {W V : ResolutionDiagram.{u}}
    (f : W ⟶ V) (hf : reedyFibrations f) :
    fibrations DaggerSSet.{u} (f.app (op ⦋0⦌)) := by
  rw [← relativeMatchingMap_zero f]
  exact ((fibrations DaggerSSet.{u}).cancel_right_of_respectsIso
    (relativeMatchingMap 0 f) (relativeMatchingZeroTargetIso f).hom).2 (hf 0)

/-- Evaluation at zero carries a Reedy cofibration to a dagger Joyal cofibration. -/
theorem reedyCofibration_evalZero {W V : ResolutionDiagram.{u}}
    (f : W ⟶ V) (hf : reedyCofibrations f) :
    cofibrations DaggerSSet.{u} (f.app (op ⦋0⦌)) := by
  rw [← relativeLatchingMap_zero f]
  exact ((cofibrations DaggerSSet.{u}).cancel_left_of_respectsIso
    (relativeLatchingZeroSourceIso f).inv (relativeLatchingMap 0 f)).2 (hf 0)

/-- The class with trivial fibration relative matching maps. -/
def relativeTrivialMatchingFibrations : MorphismProperty ResolutionDiagram.{u} :=
  reedyMatchingProperty (trivialFibrations DaggerSSet.{u})

/-- The class with trivial cofibration relative latching maps. -/
def relativeTrivialLatchingCofibrations : MorphismProperty ResolutionDiagram.{u} :=
  reedyLatchingProperty (trivialCofibrations DaggerSSet.{u})

/-- Lifting for the cofibration and relative trivial matching classes. -/
theorem reedyCofibration_lifts_relativeTrivialMatching {X Y U V : ResolutionDiagram.{u}}
    {i : X ⟶ Y} {p : U ⟶ V} (hi : reedyCofibrations i)
    (hp : relativeTrivialMatchingFibrations p) : HasLiftingProperty i p :=
  reedyLiftingOfRelativeMaps (fun n ↦ hasLiftingProperty_of_wfs
    (W₁ := cofibrations DaggerSSet.{u}) (W₂ := trivialFibrations DaggerSSet.{u})
    (relativeLatchingMap n i) (relativeMatchingMap n p) (hi n) (hp n))

/-- Lifting for the relative trivial latching and fibration classes. -/
theorem relativeTrivialLatching_lifts_reedyFibration {X Y U V : ResolutionDiagram.{u}}
    {i : X ⟶ Y} {p : U ⟶ V} (hi : relativeTrivialLatchingCofibrations i)
    (hp : reedyFibrations p) : HasLiftingProperty i p :=
  reedyLiftingOfRelativeMaps (fun n ↦ hasLiftingProperty_of_wfs
    (W₁ := trivialCofibrations DaggerSSet.{u}) (W₂ := fibrations DaggerSSet.{u})
    (relativeLatchingMap n i) (relativeMatchingMap n p) (hi n) (hp n))

/-- The first relative weak factorization system for the dagger Joyal coefficients. -/
theorem reedyCofibration_relativeTrivialMatching_wfs :
    IsWeakFactorizationSystem reedyCofibrations.{u} relativeTrivialMatchingFibrations.{u} :=
  reedyRelativeWeakFactorizationSystem (cofibrations DaggerSSet.{u})
    (trivialFibrations DaggerSSet.{u})

/-- The second relative weak factorization system for the dagger Joyal coefficients. -/
theorem relativeTrivialLatching_reedyFibration_wfs :
    IsWeakFactorizationSystem relativeTrivialLatchingCofibrations.{u} reedyFibrations.{u} :=
  reedyRelativeWeakFactorizationSystem (trivialCofibrations DaggerSSet.{u})
    (fibrations DaggerSSet.{u})

/-- Relative trivial matching maps characterize the levelwise weak Reedy fibrations. -/
theorem reedyFibrations_inf_weakEquivalences :
    reedyFibrations.{u} ⊓ reedyWeakEquivalences.{u} =
      relativeTrivialMatchingFibrations.{u} :=
  simplicialReedyFibrations_inf_weakEquivalences DaggerSSet.{u}

/-- Evaluation at any degree sends a Reedy fibration to a dagger Joyal fibration. -/
theorem reedyFibration_eval {W V : ResolutionDiagram.{u}}
    (f : W ⟶ V) (hf : reedyFibrations f) (n : ℕ) :
    fibrations DaggerSSet.{u} (f.app (op ⦋n⦌)) := by
  exact reedyMatchingFibration_eval f hf n

/-- Evaluation at any degree preserves the intersection defining trivial fibrations. -/
theorem reedyTrivialFibration_eval {W V : ResolutionDiagram.{u}}
    (f : W ⟶ V) (hf : (reedyFibrations ⊓ reedyWeakEquivalences) f) (n : ℕ) :
    trivialFibrations DaggerSSet.{u} (f.app (op ⦋n⦌)) :=
  ⟨reedyFibration_eval f hf.1 n, hf.2 _⟩

/-- Relative trivial latching maps characterize the levelwise weak Reedy cofibrations. -/
theorem reedyCofibrations_inf_weakEquivalences :
    reedyCofibrations.{u} ⊓ reedyWeakEquivalences.{u} =
      relativeTrivialLatchingCofibrations.{u} :=
  simplicialReedyCofibrations_inf_weakEquivalences DaggerSSet.{u}

/-- A Reedy cofibration is a dagger Joyal cofibration at every degree. -/
theorem reedyCofibration_eval {W V : ResolutionDiagram.{u}}
    (f : W ⟶ V) (hf : reedyCofibrations f) (n : ℕ) :
    cofibrations DaggerSSet.{u} (f.app (op ⦋n⦌)) := by
  let P := cofibrations DaggerSSet.{u}
  have hm : P ((latchingFunctor n).map f) := by
    change cofibrations DaggerSSet.{u} ((latchingFunctor n).map f)
    rw [← llp_eq_of_wfs (cofibrations DaggerSSet.{u}) (trivialFibrations DaggerSSet.{u})]
    apply latchingFunctor_map_llp
    intro m _
    rw [llp_eq_of_wfs (cofibrations DaggerSSet.{u}) (trivialFibrations DaggerSSet.{u})]
    exact hf m
  rw [← inl_comp_relativeLatchingMap f n]
  exact P.comp_mem _ _ (P.pushout_inl _ _ hm) (hf n)

/-- The Reedy model structure with levelwise dagger Joyal weak equivalences. -/
def resolutionReedyModelCategory : ModelCategory ResolutionDiagram.{u} :=
  simplicialReedyModelCategory DaggerSSet.{u}

end

end DaggerModels.PartII
