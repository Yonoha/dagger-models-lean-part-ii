/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Model structure on Over categories without the capital slice-subcategory import

Let `C` be a model category. For any `S : C`, we define
a model category structure on the category `Over S`:
a morphism `X ⟶ Y` in `Over S` is a cofibration
(resp. a fibration, a weak equivalence) if the
underlying morphism `f.left : X.left ⟶ Y.left` is.
(Apart from the existence of (finite) limits
from `Mathlib.CategoryTheory.Limits.Constructions.Over.Basic`, the verification
of the axioms is straightforward.)

## TODO
* Proceed to the dual construction for `Under S`.

-/

@[expose] public section

universe v u

open CategoryTheory

/-! The following six lowercase slice-property declarations and factorization
instance are selected from Mathlib.CategoryTheory.MorphismProperty.Comma.
The capital `MorphismProperty.Over` subcategory and its unrelated API are
intentionally absent, so this exact native Over model can coexist with the
retained Part I namespace. -/
namespace CategoryTheory.MorphismProperty

variable {T : Type*} [Category* T] {X : T} {W : MorphismProperty T}

/-- The morphism property on `Over X` induced by a property on `T`. -/
def over (W : MorphismProperty T) {X : T} :
    MorphismProperty (CategoryTheory.Over X) := fun _ _ f ↦ W f.left

lemma over_eq_inverseImage (W : MorphismProperty T) (X : T) :
    W.over = W.inverseImage (CategoryTheory.Over.forget X) := rfl

@[simp] lemma over_iff {Y Z : CategoryTheory.Over X} (f : Y ⟶ Z) :
    W.over f ↔ W f.left := .rfl

/-- The morphism property on `Under X` induced by a property on `T`. -/
def under (W : MorphismProperty T) {X : T} :
    MorphismProperty (CategoryTheory.Under X) := fun _ _ f ↦ W f.right

lemma under_eq_inverseImage (W : MorphismProperty T) (X : T) :
    W.under = W.inverseImage (CategoryTheory.Under.forget X) := rfl

@[simp] lemma under_iff {Y Z : CategoryTheory.Under X} (f : Y ⟶ Z) :
    W.under f ↔ W f.right := .rfl

instance HasFactorization.over
    {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.HasFactorization W₂] (S : C) :
    (W₁.over (X := S)).HasFactorization W₂.over where
  nonempty_mapFactorizationData {X Y} f := by
    let hf := W₁.factorizationData W₂ f.left
    exact ⟨{
      Z := .mk (hf.p ≫ Y.hom)
      i := CategoryTheory.Over.homMk hf.i
      p := CategoryTheory.Over.homMk hf.p
      hi := hf.hi
      hp := hf.hp
    }⟩

end CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (S : C)

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

instance : CategoryWithCofibrations (Over S) where
  cofibrations := (cofibrations C).over

lemma cofibrations_over_def :
    cofibrations (Over S) = (cofibrations C).over := rfl

lemma cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.left := by
  simp only [cofibration_iff, cofibrations_over_def, MorphismProperty.over_iff]

instance {X Y : Over S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.left := by
  rwa [← cofibrations_over_iff]

instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Over S)).IsStableUnderRetracts := by
  rw [cofibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

instance : CategoryWithFibrations (Over S) where
  fibrations := (fibrations C).over

lemma fibrations_over_def :
    fibrations (Over S) = (fibrations C).over := rfl

lemma fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.left := by
  simp only [fibration_iff, fibrations_over_def, MorphismProperty.over_iff]

instance {X Y : Over S} (f : X ⟶ Y) [Fibration f] : Fibration f.left := by
  rwa [← fibrations_over_iff]

instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Over S)).IsStableUnderRetracts := by
  rw [fibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

instance : CategoryWithWeakEquivalences (Over S) where
  weakEquivalences := (weakEquivalences C).over

lemma weakEquivalences_over_def :
    weakEquivalences (Over S) = (weakEquivalences C).over := rfl

lemma weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.left := by
  simp only [weakEquivalence_iff, weakEquivalences_over_def, MorphismProperty.over_iff]

instance {X Y : Over S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.left := by
  rwa [← weakEquivalences_over_iff]

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Over S)).IsStableUnderRetracts := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

lemma trivialCofibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Over S) = (trivialCofibrations C).over := rfl

lemma trivialFibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Over S) = (trivialFibrations C).over := rfl

instance [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Over S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Over S)).HasFactorization (fibrations (Over S)) := by
  rw [fibrations_over_def, trivialCofibrations_over_eq]
  infer_instance

instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Over S)).HasFactorization (trivialFibrations (Over S)) := by
  rw [cofibrations_over_def, trivialFibrations_over_eq]
  infer_instance

end

instance ModelCategory.over [ModelCategory C] : ModelCategory (Over S) where
  cm4a _ _ _ _ _ := .over _ _
  cm4b _ _ _ _ _ := .over _ _

end HomotopicalAlgebra
