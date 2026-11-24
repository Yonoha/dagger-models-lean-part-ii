import OriginalInitialCategoryCompletionThin
import OriginalCodiscreteNerveInjective
import NativeGroupoidNerveKan
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Fin

/-!
# The groupoid-completed simplex used by Joyal–Tierney

The parameter is the nerve of Mathlib's actual free groupoid on the ordered
simplex category. Its comparison with the codiscrete groupoid is a natural
isomorphism of categories, not an assumed weak equivalence. Contractibility
then follows from the retained injectivity theorem for codiscrete nerves.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.GroupoidSimplex

noncomputable section

/-- The literal groupoid completion of the finite ordered simplex. -/
abbrev completion (k : SimplexCategory) := FreeGroupoid (Fin (k.len + 1))

private local instance completionThin (k : SimplexCategory) : Quiver.IsThin (completion k) :=
  DaggerOriginalInitialCategoryCompletionThin.completionIsThin
    (0 : Fin (k.len + 1)) (Fin.isInitialZero _)

/-- The groupoid-completed simplex, as a functor to categories. -/
def completionFunctor : SimplexCategory ⥤ Cat.{0, 0} :=
  SimplexCategory.toCat ⋙ Grpd.free ⋙ Grpd.forgetToCat

/-- The actual cosimplicial Kan parameter `J^k = N G[k]`. -/
def parameter : SimplexCategory ⥤ SSet.{0} := completionFunctor ⋙ nerveFunctor

/-- The finite vertex set of the ordered simplex. -/
def vertices : SimplexCategory ⥤ Type := SimplexCategory.toCat ⋙ Cat.objects

/-- The codiscrete groupoid on the same vertices. -/
def codiscreteFunctor : SimplexCategory ⥤ Cat.{0, 0} :=
  vertices ⋙ Codiscrete.functorToCat

private def toCodiscrete (k : SimplexCategory) :
    completion k ⥤ Codiscrete (Fin (k.len + 1)) :=
  Codiscrete.functor (fun x ↦ x.as.as)

private def fromCodiscrete (k : SimplexCategory) :
    Codiscrete (Fin (k.len + 1)) ⥤ completion k where
  obj x := FreeGroupoid.mk x.as
  map {_ _} _ := Classical.choice
    (DaggerOriginalInitialCategoryCompletionThin.completionHomNonempty
      (0 : Fin (k.len + 1)) (Fin.isInitialZero _) _ _)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The completion is strictly isomorphic to the codiscrete groupoid on its vertices. -/
def completionCodiscreteIso (k : SimplexCategory) :
    completionFunctor.obj k ≅ codiscreteFunctor.obj k where
  hom := (toCodiscrete k).toCatHom
  inv := (fromCodiscrete k).toCatHom
  hom_inv_id := by
    apply Cat.ext
    change toCodiscrete k ⋙ fromCodiscrete k = 𝟭 _
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (by intros; exact Subsingleton.elim _ _)
  inv_hom_id := by
    apply Cat.ext
    change fromCodiscrete k ⋙ toCodiscrete k = 𝟭 _
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (by intros; exact Subsingleton.elim _ _)

/-- The comparison respects every simplex operator. -/
def completionCodiscreteNatIso : completionFunctor ≅ codiscreteFunctor :=
  NatIso.ofComponents completionCodiscreteIso (by
    intro k l f
    apply Cat.ext
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (by intros; rfl))

/-- The completed-simplex nerve is naturally the codiscrete nerve of its vertices. -/
def parameterCodiscreteIso :
    parameter ≅ vertices ⋙ DaggerOriginalCodiscreteNerveInjective.codiscreteNerve :=
  Functor.isoWhiskerRight completionCodiscreteNatIso nerveFunctor

/-- The actual parameter has trivial-fibration augmentation to the terminal simplex. -/
theorem augmentation_trivialFibration (k : SimplexCategory) :
    trivialFibrations SSet.{0} (terminal.from (parameter.obj k)) := by
  let e := parameterCodiscreteIso.app k
  let q := terminal.from
    (DaggerOriginalCodiscreteNerveInjective.codiscreteNerve.obj (Fin (k.len + 1)))
  have hq := DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration
    q terminalIsTerminal
  haveI : Fibration q := (fibration_iff q).mpr hq.1
  haveI : WeakEquivalence q := (weakEquivalence_iff q).mpr hq.2
  have h : e.hom ≫ q = terminal.from (parameter.obj k) :=
    terminalIsTerminal.hom_ext _ _
  rw [← h]
  exact ⟨(fibration_iff _).mp inferInstance, (weakEquivalence_iff _).mp inferInstance⟩

/-- Each groupoid-completed simplex is a Kan complex. -/
theorem parameter_kan (k : SimplexCategory) : (parameter.obj k).KanComplex := by
  exact DaggerNativeGroupoidNerveKan.nerve_kan (completion k)

end

end DaggerModels.PartII.GroupoidSimplex
