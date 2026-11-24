import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Weak cofibrations and arbitrary cobase change

Left properness for weak maps pushed along cofibrations, together with a
cofibration–weak-right factorization, makes weak cofibrations stable under
arbitrary cobase change. The proof uses the actual supplied pushout square.
No model-category structure is assumed.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe v u

namespace DaggerModels.PartII.WeakCofibrationCobase

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  (Cof W TF : MorphismProperty C)
  [Cof.IsStableUnderCobaseChange] [W.HasTwoOutOfThreeProperty]
  [Cof.HasFactorization TF]

/-- A weak cofibration remains weak under every supplied pushout when weak
maps are left proper along cofibrations and the right factorization class is
weak. -/
theorem weak_of_isPushout
    (hTF : TF ≤ W)
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D}
      {l : B ⟶ P} {r : D ⟶ P},
      IsPushout i k l r → Cof i → W k → W l)
    {A B D P : C} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P}
    (sq : IsPushout i k l r) (hi : Cof i ∧ W i) : W r := by
  let d := factorizationData Cof TF k
  let a : B ⟶ pushout i d.i := pushout.inl i d.i
  let b : d.Z ⟶ pushout i d.i := pushout.inr i d.i
  have hcond : i ≫ l = d.i ≫ (d.p ≫ r) := by
    rw [← Category.assoc, d.fac]
    exact sq.w
  let q : pushout i d.i ⟶ P := pushout.desc l (d.p ≫ r) hcond
  have hA : a ≫ q = l := pushout.inl_desc _ _ _
  have hB : b ≫ q = d.p ≫ r := pushout.inr_desc _ _ _
  have sq₁ : IsPushout i d.i a b := IsPushout.of_hasPushout i d.i
  have hbCof : Cof b := Cof.of_isPushout sq₁.flip hi.1
  have hbWeak : W b := leftProper sq₁.flip d.hi hi.2
  have hOuter : IsPushout i (d.i ≫ d.p) (a ≫ q) r := by
    rw [d.fac, hA]
    exact sq
  have sq₂ : IsPushout b d.p q r := hOuter.of_top hB sq₁
  have hqWeak : W q := leftProper sq₂ hbCof (hTF d.p d.hp)
  have hcomp : W (d.p ≫ r) := by
    rw [← hB]
    exact W.comp_mem b q hbWeak hqWeak
  exact W.of_precomp d.p r (hTF d.p d.hp) hcomp

/-- Under the same generic hypotheses, the intersection of cofibrations and
weak equivalences is stable under all actual cobase changes. -/
def stableUnderCobaseChange
    (hTF : TF ≤ W)
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D}
      {l : B ⟶ P} {r : D ⟶ P},
      IsPushout i k l r → Cof i → W k → W l) :
    (Cof ⊓ W).IsStableUnderCobaseChange where
  of_isPushout sq hi :=
    ⟨Cof.of_isPushout sq hi.1,
      weak_of_isPushout Cof W TF hTF leftProper sq.flip hi⟩

end DaggerModels.PartII.WeakCofibrationCobase
