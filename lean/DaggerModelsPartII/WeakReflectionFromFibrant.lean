import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Weak-equivalence reflection from fibrant objects

A weak-equivalence-preserving functor between model categories reflects all
weak equivalences if it reflects weak equivalences between fibrant objects.
The proof compares two ordinary fibrant replacements using a lifting square.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u v

namespace DaggerModels.PartII.WeakReflectionFromFibrant

noncomputable section

/-- Reflection on fibrant objects extends to all arrows when the functor
preserves every weak equivalence. -/
theorem reflects_weakEquivalences
    {C : Type u} {D : Type v} [Category C] [Category D]
    [ModelCategory C] [ModelCategory D] (F : C ⥤ D)
    (hpres : ∀ {X Y : C} (f : X ⟶ Y),
      (weakEquivalences C) f → (weakEquivalences D) (F.map f))
    (href : ∀ {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y),
      (weakEquivalences D) (F.map f) → (weakEquivalences C) f)
    {X Y : C} (f : X ⟶ Y)
    (hf : (weakEquivalences D) (F.map f)) :
    (weakEquivalences C) f := by
  let a := MorphismProperty.factorizationData
    (trivialCofibrations C) (fibrations C) (terminal.from X)
  let b := MorphismProperty.factorizationData
    (trivialCofibrations C) (fibrations C) (terminal.from Y)
  haveI : IsFibrant a.Z := by
    change Fibration (terminal.from a.Z)
    have heq : a.p = terminal.from a.Z := terminalIsTerminal.hom_ext _ _
    rw [← heq]
    exact (fibration_iff _).mpr a.hp
  haveI : IsFibrant b.Z := by
    change Fibration (terminal.from b.Z)
    have heq : b.p = terminal.from b.Z := terminalIsTerminal.hom_ext _ _
    rw [← heq]
    exact (fibration_iff _).mpr b.hp
  let sq : CommSq (f ≫ b.i) a.i b.p a.p := CommSq.mk (by
    rw [Category.assoc, b.fac, a.fac]
    exact terminalIsTerminal.hom_ext _ _)
  haveI : Cofibration a.i := (cofibration_iff _).mpr a.hi.1
  haveI : WeakEquivalence a.i := (weakEquivalence_iff _).mpr a.hi.2
  haveI : Fibration b.p := (fibration_iff _).mpr b.hp
  letI : HasLiftingProperty a.i b.p := inferInstance
  let g : a.Z ⟶ b.Z := sq.lift
  have hs : a.i ≫ g = f ≫ b.i := sq.fac_left
  have hFb : (weakEquivalences D) (F.map b.i) := hpres b.i b.hi.2
  have hFa : (weakEquivalences D) (F.map a.i) := hpres a.i a.hi.2
  have hFcomp : (weakEquivalences D) (F.map (a.i ≫ g)) := by
    rw [hs, F.map_comp]
    exact (weakEquivalences D).comp_mem _ _ hf hFb
  have hFg : (weakEquivalences D) (F.map g) := by
    apply (weakEquivalences D).of_precomp (F.map a.i) (F.map g) hFa
    simpa only [← F.map_comp] using hFcomp
  have hg : (weakEquivalences C) g := href g hFg
  have hcomp : (weakEquivalences C) (f ≫ b.i) := by
    rw [← hs]
    exact (weakEquivalences C).comp_mem _ _ a.hi.2 hg
  exact (weakEquivalences C).of_postcomp f b.i b.hi.2 hcomp

end

end DaggerModels.PartII.WeakReflectionFromFibrant
