import DaggerModelsPartII.WeakFunctorBrown
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Transport from one cofibrant replacement to every cofibrant replacement

A functor preserving trivial cofibrations into an explicit weak class need
only carry one cofibrant weak augmentation to a weak map. Every other weak
augmentation with cofibrant source then has weak image. The target object
of the augmentations need not be cofibrant.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra

universe v u v' u'

namespace DaggerModels.PartII.WeakFunctorReplacement

noncomputable section

/-- Weakness of the image of one cofibrant weak augmentation is independent
of the choice of cofibrant weak augmentation, without target cofibrancy. -/
theorem map_weak_of_cofibrant_augmentation
    {C : Type u} [Category.{v} C] [ModelCategory C]
    [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) (W : MorphismProperty D)
    [W.ContainsIdentities] [W.HasTwoOutOfThreeProperty]
    (hTC : ∀ {A B : C} (i : A ⟶ B), trivialCofibrations C i → W (F.map i))
    {A B X : C} [IsCofibrant A] [IsCofibrant B]
    (e : B ⟶ X) (he : weakEquivalences C e) (hFe : W (F.map e))
    (q : A ⟶ X) (hq : weakEquivalences C q) : W (F.map q) := by
  let d := MorphismProperty.factorizationData
    (cofibrations C) (trivialFibrations C) q
  have hi : weakEquivalences C d.i := by
    apply (weakEquivalences C).of_postcomp d.i d.p d.hp.2
    rw [d.fac]
    exact hq
  have : Cofibration d.i := (cofibration_iff _).2 d.hi
  have : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
  have : Fibration d.p := (fibration_iff _).2 d.hp.1
  have : WeakEquivalence d.p := (weakEquivalence_iff _).2 d.hp.2
  let sq : CommSq (initial.to d.Z) (initial.to B) d.p e :=
    CommSq.mk (initialIsInitial.hom_ext _ _)
  let l : B ⟶ d.Z := sq.lift
  have hlp : l ≫ d.p = e := sq.fac_right
  have hl : weakEquivalences C l := by
    apply (weakEquivalences C).of_postcomp l d.p d.hp.2
    rw [hlp]
    exact he
  have hFl : W (F.map l) :=
    WeakFunctorBrown.map_weak_on_cofibrant F W hTC l hl
  have hFp : W (F.map d.p) := by
    apply W.of_precomp (F.map l) _ hFl
    rw [← F.map_comp, hlp]
    exact hFe
  rw [← d.fac, F.map_comp]
  exact W.comp_mem _ _ (hTC d.i ⟨d.hi, hi⟩) hFp

end

end DaggerModels.PartII.WeakFunctorReplacement
