import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Brown preservation with an explicit target weak class

The target needs only identities and weak two-of-three. The native source
model provides the actual cofibrant Brown factorization. No model structure
or factorization on the target is assumed.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe v u v' u'

namespace DaggerModels.PartII.WeakFunctorBrown

/-- A functor carrying source trivial cofibrations into an explicit target
weak class carries every weak map between cofibrant objects into that class. -/
theorem map_weak_on_cofibrant
    {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) (W : MorphismProperty D)
    [W.ContainsIdentities] [W.HasTwoOutOfThreeProperty]
    (hTC : ∀ {A B : C} (i : A ⟶ B), trivialCofibrations C i → W (F.map i))
    {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
    (hf : weakEquivalences C f) : W (F.map f) := by
  have : WeakEquivalence f := (weakEquivalence_iff f).2 hf
  let d := (inferInstance : Nonempty (CofibrantBrownFactorization f)).some
  have hi : W (F.map d.i) := hTC d.i (mem_trivialCofibrations d.i)
  have hs : W (F.map d.s) := hTC d.s (mem_trivialCofibrations d.s)
  have hp : W (F.map d.p) := by
    apply W.of_precomp (F.map d.s) _ hs
    rw [← F.map_comp, d.s_p, F.map_id]
    exact W.id_mem _
  rw [← d.fac, F.map_comp]
  exact W.comp_mem _ _ hi hp

end DaggerModels.PartII.WeakFunctorBrown
