import DaggerModelsPartII.DiagonalInvolutionOrbits
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Simplicial diagonal orbits of a discrete involution

The quotient is taken in every simplicial degree, with every simplicial
operator induced from the second factor. For a free discrete first factor,
the quotient is naturally a family of copies of the second simplicial set.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerModels.PartII.BorelDiscreteOrbits

open DaggerModels.FreeInvolution DiagonalInvolutionOrbits

noncomputable section

variable (E : SSet.{u}) (σ : E ≅ E) (hσ : σ.hom ≫ σ.hom = 𝟙 E)

/-- The involution on simplices in a fixed degree. -/
def degreeEquiv (n : SimplexCategoryᵒᵖ) : E.obj n ≃ E.obj n := (σ.app n).toEquiv

include hσ in
theorem degree_involutive (n : SimplexCategoryᵒᵖ) :
    Function.Involutive (degreeEquiv E σ n) := by
  intro x
  exact congrFun (congr_app hσ n) x

theorem degree_comm {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : E.obj n) :
    E.map f (degreeEquiv E σ n x) = degreeEquiv E σ m (E.map f x) :=
  (congrFun (σ.hom.naturality f) x).symm

variable {X : Type u} (τ : X ≃ X) (hτ : Function.Involutive τ)

/-- The literal simplicial quotient of the product by its diagonal involution. -/
def borel : SSet.{u} where
  obj n := DiagonalOrbit τ hτ (degreeEquiv E σ n) (degree_involutive E σ hσ n)
  map {n m} f := secondMap τ hτ
    (degreeEquiv E σ n) (degree_involutive E σ hσ n)
    (degreeEquiv E σ m) (degree_involutive E σ hσ m)
    (E.map f) (degree_comm E σ f)
  map_id n := by
    funext q
    induction q using Quotient.inductionOn with
    | _ p =>
      change orbit _ _ (p.1, E.map (𝟙 n) p.2) = orbit _ _ (p.1, p.2)
      rw [E.map_id]
      rfl
  map_comp f g := by
    funext q
    induction q using Quotient.inductionOn with
    | _ p =>
      change orbit _ _ (p.1, E.map (f ≫ g) p.2) =
        orbit _ _ (p.1, E.map g (E.map f p.2))
      rw [E.map_comp]
      rfl

/-- A family of copies indexed by a fixed discrete set. -/
def copies (T : Type u) : SSet.{u} where
  obj n := T × E.obj n
  map f p := (p.1, E.map f p.2)
  map_id n := by
    funext p
    simp only [E.map_id]
    rfl
  map_comp f g := by
    funext p
    simp only [E.map_comp]
    rfl

/-- Free diagonal orbits are a family of copies, naturally for all simplicial operators. -/
def cancellationIso (hfree : ∀ x, τ x ≠ x) :
    borel E σ hσ τ hτ ≅ copies E (Orbit τ hτ) :=
  NatIso.ofComponents
    (fun n ↦ Equiv.toIso (cancellation τ hτ (degreeEquiv E σ n)
      (degree_involutive E σ hσ n) hfree)) (by
    intro n m f
    funext q
    exact cancellation_secondMap τ hτ (degreeEquiv E σ n)
      (degree_involutive E σ hσ n) hfree (degreeEquiv E σ m)
      (degree_involutive E σ hσ m) (E.map f) (degree_comm E σ f) q)

/-- The collapse to the strict orbit set of the discrete factor. -/
def collapse : borel E σ hσ τ hτ ⟶ (SimplicialObject.const (Type u)).obj (Orbit τ hτ) where
  app n := projection τ hτ (degreeEquiv E σ n) (degree_involutive E σ hσ n)
  naturality n m f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ p => rfl

/-- Forget the simplicial coordinate in a family of copies. -/
def copiesProjection (T : Type u) :
    copies E T ⟶ (SimplicialObject.const (Type u)).obj T where
  app _ := Prod.fst
  naturality _ _ _ := rfl

/-- Under cancellation, the Borel collapse is exactly the family projection. -/
theorem cancellationIso_collapse (hfree : ∀ x, τ x ≠ x) :
    (cancellationIso E σ hσ τ hτ hfree).hom ≫ copiesProjection E (Orbit τ hτ) =
      collapse E σ hσ τ hτ := by
  apply NatTrans.ext
  funext n q
  exact cancellation_fst τ hτ (degreeEquiv E σ n) (degree_involutive E σ hσ n) hfree q

end

end DaggerModels.PartII.BorelDiscreteOrbits
