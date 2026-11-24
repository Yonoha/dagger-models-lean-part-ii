import DaggerModelsPartII.OrdinaryJTRealization
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Generators and relations for the actual JT realization

The native pointwise Kan-extension cocone supplies the generators. Evaluation
preserves its colimit, so every simplex comes from one of these generators.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite

namespace DaggerModels.PartII.JTRealizationGenerators

open OrdinaryJTRealization

noncomputable section

/-- The canonical coend generator specified by a parameter and a presheaf element. -/
def generator (W : BiPresheaf) (p : Index) (w : W.obj (op p)) :
    tFunctor.obj p ⟶ realization.obj W :=
  realizationUnit.app p ≫ realization.map (uliftYonedaEquiv.{0}.symm w)

/-- The generator is the corresponding leg of the actual pointwise colimit. -/
theorem generator_eq_cocone (W : BiPresheaf) (p : Index) (w : W.obj (op p)) :
    generator W p w =
      (simplexCocone W).ι.app (CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w)) := rfl

/-- The literal coend relation for an operator in either parameter. -/
theorem generator_relation (W : BiPresheaf) {p q : Index} (f : p ⟶ q)
    (w : W.obj (op q)) :
    tFunctor.map f ≫ generator W q w = generator W p (W.map f.op w) := by
  change tFunctor.map f ≫
      (realizationUnit.app q ≫ realization.map (uliftYonedaEquiv.{0}.symm w)) =
    realizationUnit.app p ≫ realization.map (uliftYonedaEquiv.{0}.symm (W.map f.op w))
  rw [← Category.assoc, realizationUnit.naturality f, Category.assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  exact congrArg (fun h ↦ realizationUnit.app p ≫ realization.map h)
    (uliftYonedaEquiv_symm_map f.op w).symm

/-- The generators commute with every natural transformation of input presheaves. -/
theorem generator_naturality {W V : BiPresheaf} (g : W ⟶ V)
    (p : Index) (w : W.obj (op p)) :
    generator W p w ≫ realization.map g = generator V p (g.app (op p) w) := by
  dsimp [generator]
  rw [Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg realization.map
  apply uliftYonedaEquiv.{0}.injective
  rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Every simplex of the actual realization is represented by one parameter simplex. -/
theorem exists_generator (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (x : (realization.obj W).obj n) :
    ∃ (p : Index) (w : W.obj (op p)) (s : (tFunctor.obj p).obj n),
      (generator W p w).app n s = x := by
  let E : SSet.{0} ⥤ Type := (evaluation _ _).obj n
  obtain ⟨σ, s, hs⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves E (simplexCoconeIsColimit W)) x
  refine ⟨σ.left, uliftYonedaEquiv.{0} σ.hom, s, ?_⟩
  simpa only [generator, Equiv.symm_apply_apply] using hs

end

end DaggerModels.PartII.JTRealizationGenerators
