import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! Natural maps into a diagram of specified pullback squares. -/

set_option autoImplicit false

open CategoryTheory Limits

namespace DaggerModels.PartII.JTPointwisePullbackLift

universe u v w z

variable {J : Type u} [Category.{v} J] {C : Type w} [Category.{z} C]
variable {P X Y Z W : J ⥤ C} (fst : P ⟶ X) (snd : P ⟶ Y)
variable (f : X ⟶ Z) (g : Y ⟶ Z)
variable (h : ∀ i, IsPullback (fst.app i) (snd.app i) (f.app i) (g.app i))
variable (a : W ⟶ X) (b : W ⟶ Y)
variable (w : ∀ i, a.app i ≫ f.app i = b.app i ≫ g.app i)

/-- The pointwise pullback lifts of two compatible natural transformations
form a natural transformation with both specified projections. -/
noncomputable def lift : W ⟶ P where
  app i := (h i).lift (a.app i) (b.app i) (w i)
  naturality {i j} k := by
    apply (h j).hom_ext
    · calc
        _ = W.map k ≫ a.app j := by rw [Category.assoc, (h j).lift_fst]
        _ = a.app i ≫ X.map k := a.naturality k
        _ = _ := by rw [Category.assoc, fst.naturality, ← Category.assoc, (h i).lift_fst]
    · calc
        _ = W.map k ≫ b.app j := by rw [Category.assoc, (h j).lift_snd]
        _ = b.app i ≫ Y.map k := b.naturality k
        _ = _ := by rw [Category.assoc, snd.naturality, ← Category.assoc, (h i).lift_snd]

theorem lift_fst (i : J) : (lift fst snd f g h a b w).app i ≫ fst.app i = a.app i :=
  (h i).lift_fst _ _ _

theorem lift_snd (i : J) : (lift fst snd f g h a b w).app i ≫ snd.app i = b.app i :=
  (h i).lift_snd _ _ _

end DaggerModels.PartII.JTPointwisePullbackLift
