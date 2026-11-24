import DaggerModelsPartII.InjectiveKanDiagramDensity
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.AlgebraicTopology.SimplicialSet.RegularEpi

set_option autoImplicit false
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

theorem diagramHasStrongEpiMonoFactorisations :
    HasStrongEpiMonoFactorisations (C ⥤ SSet.{u}) := by
  letI : HasStrongEpiMonoFactorisations
    (C × SimplexCategoryᵒᵖ ⥤ Type u) := inferInstance
  letI : Functor.IsEquivalence (Functor.curry : (C × SimplexCategoryᵒᵖ ⥤ Type u) ⥤
      (C ⥤ SSet.{u})) := (Functor.currying :
        (C ⥤ SSet.{u}) ≌ (C × SimplexCategoryᵒᵖ ⥤ Type u)).isEquivalence_inverse
  exact Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    (Functor.curry : (C × SimplexCategoryᵒᵖ ⥤ Type u) ⥤
      (C ⥤ SSet.{u}))

/-- A natural transformation of simplicial-set diagrams has an image
factorization with regular-epi first map and monic second map. -/
theorem exists_regularEpi_mono_factorization {F G : C ⥤ SSet.{u}}
    (f : F ⟶ G) :
    ∃ (Q : C ⥤ SSet.{u}) (e : F ⟶ Q) (m : Q ⟶ G),
      e ≫ m = f ∧ IsRegularEpi e ∧ Mono m := by
  letI : HasStrongEpiMonoFactorisations (C ⥤ SSet.{u}) :=
    diagramHasStrongEpiMonoFactorisations C
  let H : StrongEpiMonoFactorisation f :=
    (HasStrongEpiMonoFactorisations.has_fac f).some
  refine ⟨H.I, H.e, H.m, H.fac, ?_, inferInstance⟩
  haveI : IsRegularEpiCategory (C ⥤ SSet.{u}) := inferInstance
  exact IsRegularEpiCategory.regularEpiOfEpi H.e


/-- For any map from a free simplex diagram, its cyclic image is a regular-epi
quotient, and the small generators test all subobjects of that image. -/
theorem quotientSubobjectGenerators_rlp_cyclicImage
    {X Y G : C ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : (quotientSubobjectGenerators C).rlp p)
    (c : C) (n : ℕ) (f : freeSimplexDiagram C c n ⟶ G) :
    ∃ (Q : C ⥤ SSet.{u}) (e : freeSimplexDiagram C c n ⟶ Q)
      (m : Q ⟶ G),
      e ≫ m = f ∧ IsRegularEpi e ∧ Mono m ∧
        ∀ (S : Subobject Q), HasLiftingProperty S.arrow p := by
  obtain ⟨Q, e, m, h, he, hm⟩ :=
    exists_regularEpi_mono_factorization C f
  letI : IsRegularEpi e := he
  exact ⟨Q, e, m, h, he, hm,
    fun S => quotientSubobjectGenerators_rlp_regularEpi_subobject C p hp c n Q e S⟩

end
end DaggerModels.PartII.InjectiveKanDiagram
