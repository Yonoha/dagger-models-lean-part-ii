import DaggerModelsPartII.JTRealizationGenerators
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Presentations of an actual JT realization simplex

The native pointwise left-Kan-extension diagram is evaluated at one simplicial
degree. Its category of elements retains both JT indices and the actual
operator relations. The cocone value defines a functor to the discrete set of
realized simplices. The comma category over a specified simplex is nonempty
by the checked generator-coverage theorem. No homotopy finality, contractibility,
or natural choice of a presentation is asserted here.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTRealizationSimplexPresentations

open OrdinaryJTRealization JTRealizationGenerators

noncomputable section

/-- The **evaluated actual** simplex diagram, with its two-index operators. -/
def degreeDiagram (W : BiPresheaf) (n : SimplexCategoryᵒᵖ) :
    SimplexIndex W ⥤ Type :=
  simplexDiagram W ⋙ (evaluation SimplexCategoryᵒᵖ Type).obj n

/-- An object is one actual coend parameter together with a simplex in its
JT weight. The category structure is Mathlib's category of elements. -/
abbrev DegreeElements (W : BiPresheaf) (n : SimplexCategoryᵒᵖ) :=
  (degreeDiagram W n).Elements

/-- The value of a presentation under the original pointwise cocone. -/
def value (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (e : DegreeElements W n) : (realization.obj W).obj n :=
  ((simplexCocone W).ι.app e.1).app n e.2

/-- A morphism of native presentations preserves its realized simplex. -/
theorem value_eq_of_hom (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    {e e' : DegreeElements W n} (f : e ⟶ e') : value W n e = value W n e' := by
  have hc := (simplexCocone W).w f.val
  have hf := CategoryOfElements.map_snd f
  calc
    value W n e =
        (((simplexDiagram W).map f.val) ≫
          (simplexCocone W).ι.app e'.1).app n e.2 := by
            exact congrArg (fun t ↦ t.app n e.2) hc.symm
    _ = ((simplexCocone W).ι.app e'.1).app n
          (((degreeDiagram W n).map f.val) e.2) := rfl
    _ = value W n e' := by simp only [hf, value]

/-- The cocone sends every presentation and every relation to the discrete
category of simplices in the **same actual** realization. -/
def valueFunctor (W : BiPresheaf) (n : SimplexCategoryᵒᵖ) :
    DegreeElements W n ⥤ Discrete ((realization.obj W).obj n) where
  obj e := ⟨value W n e⟩
  map f := Discrete.eqToHom (value_eq_of_hom W n f)
  map_id e := by apply Subsingleton.elim
  map_comp f g := by apply Subsingleton.elim

/-- The native comma/fiber category of presentations of the specified
realized `n`-simplex. Its objects carry an equality of cocone values, not a
choice of preferred generator. -/
abbrev Presentation (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (z : (realization.obj W).obj n) :=
  StructuredArrow (Discrete.mk z) (valueFunctor W n)

/-- Forget the specified value equation but keep the actual element of the
evaluated simplex diagram. -/
def forgetElement (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (z : (realization.obj W).obj n) :
    Presentation W n z ⥤ DegreeElements W n :=
  StructuredArrow.proj (Discrete.mk z) (valueFunctor W n)

/-- The projection retains the complete costructured-arrow operator,
including both ordinary JT coordinates. -/
def forgetIndex (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (z : (realization.obj W).obj n) : Presentation W n z ⥤ SimplexIndex W :=
  forgetElement W n z ⋙ CategoryOfElements.π (degreeDiagram W n)

/-- The native category-of-elements object corresponding to a specified
generator triple. -/
def generatorElement (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (p : Index) (w : W.obj (op p)) (s : (tFunctor.obj p).obj n) :
    DegreeElements W n :=
  ⟨CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w), s⟩

/-- Its cocone value is exactly the existing generator, with no new quotient
or operator convention. -/
theorem value_generator (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (p : Index) (w : W.obj (op p)) (s : (tFunctor.obj p).obj n) :
    value W n (generatorElement W n p w s) = (generator W p w).app n s := by
  rw [generator_eq_cocone]
  rfl

/-- Each realized simplex has at least one actual presentation. This is
only nonemptiness; no functorial section or categorical finality follows. -/
theorem presentation_nonempty (W : BiPresheaf) (n : SimplexCategoryᵒᵖ)
    (z : (realization.obj W).obj n) : Nonempty (Presentation W n z) := by
  obtain ⟨p, w, s, hs⟩ := exists_generator W n z
  let e := generatorElement W n p w s
  have he : value W n e = z := by
    dsimp [e]
    rw [value_generator]
    exact hs
  exact ⟨StructuredArrow.mk (Discrete.eqToHom he.symm)⟩

end

end DaggerModels.PartII.JTRealizationSimplexPresentations
