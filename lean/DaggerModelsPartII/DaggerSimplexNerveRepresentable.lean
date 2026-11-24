import DaggerModelsPartII.DaggerSimplexPartIIndex
import DaggerModelsPartII.ActualIndexProjectiveModel
import DaggerModelsPartII.SegalLocalizers

/-!
# Representables and the ordinary dagger nerve of a free simplex

All dagger functors from a free dagger simplex are exactly chains in its
ordinary nerve. The equivalence includes the full Hom sets of the actual
Part I index. At a reversal representable, the change-of-index unit applies
the exact functor `actualU` to each morphism.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexFreeProperty
open DaggerModels.PartII.DaggerSimplexPartIIndex

namespace DaggerModels.PartII.DaggerSimplexNerveRepresentable

noncomputable section

/-- A path-index morphism is precisely an ordinary dagger functor between
the corresponding free dagger categories. -/
def pathHomFunctorEquiv (m n : ℕ) :
    ((⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩) ≃
      {F : FreeDaggerSimplex m ⥤ FreeDaggerSimplex n // DaggerFunctor F} where
  toFun f := by
    change DaggerSimplex.Hom ⟨m⟩ ⟨n⟩ at f
    exact ⟨f.toFunctor, f.map_dagger⟩
  invFun F := ⟨F.1, F.2⟩
  left_inv f := by
    change DaggerSimplex.Hom ⟨m⟩ ⟨n⟩ at f
    cases f
    rfl
  right_inv F := by cases F; rfl

/-- Every path-index morphism is exactly an arbitrary chain of objects and
arrows in the target free dagger simplex. -/
def pathHomChainEquiv (m n : ℕ) :
    ((⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩) ≃
      (Fin (m + 1) ⥤ FreeDaggerSimplex n) :=
  (pathHomFunctorEquiv m n).trans
    (freeDaggerSimplexOrdinalEquiv m (FreeDaggerSimplex n))

/-- The same chain classification for all enriched dagger functors in the
actual Part I index, transported by the canonical comparison isomorphisms. -/
def actualHomChainEquiv (m n : ℕ) :
    ((⟨m⟩ : ActualDaggerSimplex) ⟶ ⟨n⟩) ≃
      (Fin (m + 1) ⥤ FreeDaggerSimplex n) :=
  (actualHomEquiv ⟨m⟩ ⟨n⟩).symm.trans (pathHomChainEquiv m n)

/-- The actual full Hom set is the degree-`m` set of the native ordinary
dagger nerve of the path presentation of the target free simplex. -/
def actualHomNativeNerveEquiv (m n : ℕ) :
    ((⟨m⟩ : ActualDaggerSimplex) ⟶ ⟨n⟩) ≃
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex n)).toSSet.obj
        (op ⦋m⦌) :=
  actualHomChainEquiv m n

/-- The path classification recovers the original dagger functor, including
all reversed generators and all nonreduced words. -/
theorem pathHomChainEquiv_symm_toFunctor (m n : ℕ)
    (F : Fin (m + 1) ⥤ FreeDaggerSimplex n) :
    ((pathHomChainEquiv m n).symm F).toFunctor =
      ((freeDaggerSimplexOrdinalEquiv m (FreeDaggerSimplex n)).symm F).1 := rfl

/-- The classification is natural under every dagger functor between target
free simplices, including functors that send edges to arbitrary words. -/
theorem pathHomChainEquiv_comp (m n p : ℕ)
    (f : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩)
    (g : (⟨n⟩ : DaggerSimplex) ⟶ ⟨p⟩) :
    pathHomChainEquiv m p (f ≫ g) =
      pathHomChainEquiv m n f ⋙ g.toFunctor := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    rfl
  case h_map =>
    intro i j h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    letI : DaggerFunctor f.toFunctor := f.map_dagger
    letI : DaggerFunctor g.toFunctor := g.map_dagger
    exact (wordValue_restrict m (FreeDaggerSimplex p)
      ⟨f.toFunctor ⋙ g.toFunctor, inferInstance⟩ _).trans
      (by rw [Functor.comp_map, ← wordValue_restrict m (FreeDaggerSimplex n)
        ⟨f.toFunctor, inferInstance⟩ _]; rfl)

/-- The corresponding target naturality holds for every enriched dagger
functor in the actual Part I index. -/
theorem actualHomChainEquiv_comp (m n p : ℕ)
    (f : (⟨m⟩ : ActualDaggerSimplex) ⟶ ⟨n⟩)
    (g : (⟨n⟩ : ActualDaggerSimplex) ⟶ ⟨p⟩) :
    actualHomChainEquiv m p (f ≫ g) =
      actualHomChainEquiv m n f ⋙
        ((actualHomEquiv ⟨n⟩ ⟨p⟩).symm g).toFunctor := by
  have hcomp : (actualHomEquiv ⟨m⟩ ⟨p⟩).symm (f ≫ g) =
      (actualHomEquiv ⟨m⟩ ⟨n⟩).symm f ≫
        (actualHomEquiv ⟨n⟩ ⟨p⟩).symm g := by
    apply (actualHomEquiv ⟨m⟩ ⟨p⟩).injective
    change pathToActual.map ((actualHomEquiv ⟨m⟩ ⟨p⟩).symm (f ≫ g)) =
      pathToActual.map ((actualHomEquiv ⟨m⟩ ⟨n⟩).symm f ≫
        (actualHomEquiv ⟨n⟩ ⟨p⟩).symm g)
    rw [pathToActual.map_comp]
    change (actualHomEquiv ⟨m⟩ ⟨p⟩) ((actualHomEquiv ⟨m⟩ ⟨p⟩).symm (f ≫ g)) =
      (actualHomEquiv ⟨m⟩ ⟨n⟩) ((actualHomEquiv ⟨m⟩ ⟨n⟩).symm f) ≫
      (actualHomEquiv ⟨n⟩ ⟨p⟩) ((actualHomEquiv ⟨n⟩ ⟨p⟩).symm g)
    simp
  change pathHomChainEquiv m p ((actualHomEquiv ⟨m⟩ ⟨p⟩).symm (f ≫ g)) = _
  rw [hcomp, pathHomChainEquiv_comp]
  rfl

/-- Under the standard representable comparison, the unit at a reversal
representable sends a morphism `f` to `actualU.map f` in every inner degree. -/
theorem actualUnit_representable_apply (m n : DaggerModels.ReverseSimplex)
    (q : SimplexCategoryᵒᵖ) (f : m ⟶ n) :
    (((ActualIndexProjectiveModel.actualLeftAdjunction.{0}).unit.app
      ((simplicialYoneda.{0, 0} ReverseSimplex).obj n) ≫
      (ActualIndexProjectiveModel.actualRestriction.{0}).map
        ((ActualIndexProjectiveModel.actualLeftExtension_simplicialYoneda.{0}).hom.app n)).app
      (op m)).app q (ULift.up f) = ULift.up (actualU.map f) :=
  extendIndexLeft_unit_simplicialYoneda.{0, 0} actualU n m q f

end

end DaggerModels.PartII.DaggerSimplexNerveRepresentable
