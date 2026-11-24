import DaggerModelsPartII.DaggerSimplexPartIComparison

/-!
# The manuscript's full index of free enriched dagger simplices

Objects are the actual Part I free simplicial dagger categories on the
constant finite ordinals.  Morphisms are all enriched dagger functors.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexPartIComparison

namespace DaggerModels.PartII.DaggerSimplexPartIIndex

noncomputable section

/-- An object of the exact index used in Part II. -/
structure ActualDaggerSimplex where
  len : ℕ

instance : Category ActualDaggerSimplex where
  Hom m n := partIFree m.len ⟶ partIFree n.len
  id _ := 𝟙 _
  comp f g := f ≫ g
  id_comp := by intros; exact Category.id_comp _
  comp_id := by intros; exact Category.comp_id _
  assoc := by intros; exact Category.assoc _ _ _

/-- The exact Part I free objects form a full subcategory of enriched dagger
categories, with all enriched dagger functors as its Hom sets. -/
def actualInclusion : ActualDaggerSimplex ⥤ DaggerSimplicialCat.{0, 0} where
  obj n := partIFree n.len
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : actualInclusion.Full where
  map_surjective f := ⟨f, rfl⟩

instance : actualInclusion.Faithful where
  map_injective := by
    intro m n f g h
    exact h

/-- Conjugation by the canonical Part I versus path isomorphisms identifies
every ordinary path-model dagger functor with an enriched dagger functor
between the actual Part I free objects. -/
def actualHomEquiv (m n : DaggerSimplex) :
    (m ⟶ n) ≃ (partIFree m.len ⟶ partIFree n.len) where
  toFun f :=
    ((comparisonIso m.len).hom ≫
      (enrichedDaggerSimplexHomEquiv m n) f ≫ (comparisonIso n.len).inv :
        partIFree m.len ⟶ partIFree n.len)
  invFun f := (enrichedDaggerSimplexHomEquiv m n).symm
    ((comparisonIso m.len).inv ≫ f ≫ (comparisonIso n.len).hom)
  left_inv f := by
    apply (enrichedDaggerSimplexHomEquiv m n).injective
    simp [Category.assoc]
  right_inv f := by
    simp [Category.assoc]

/-- The path-model index maps to the exact manuscript index. -/
def pathToActual : DaggerSimplex ⥤ ActualDaggerSimplex where
  obj n := ⟨n.len⟩
  map := fun {m n} f => actualHomEquiv m n f
  map_id n := by
    change (comparisonIso n.len).hom ≫
      enrichedDaggerSimplexInclusion.map (𝟙 n) ≫
      (comparisonIso n.len).inv = 𝟙 (partIFree n.len)
    rw [enrichedDaggerSimplexInclusion.map_id]
    change (comparisonIso n.len).hom ≫ 𝟙 (pathFree n.len) ≫
      (comparisonIso n.len).inv = 𝟙 (partIFree n.len)
    calc
      (comparisonIso n.len).hom ≫ 𝟙 (pathFree n.len) ≫
          (comparisonIso n.len).inv =
        ((comparisonIso n.len).hom ≫ 𝟙 (pathFree n.len)) ≫
          (comparisonIso n.len).inv := rfl
      _ = (comparisonIso n.len).hom ≫ (comparisonIso n.len).inv := by
        rw [Category.comp_id]
      _ = 𝟙 (partIFree n.len) := (comparisonIso n.len).hom_inv_id
  map_comp {m n p} f g := by
    change (comparisonIso m.len).hom ≫
      enrichedDaggerSimplexInclusion.map (f ≫ g) ≫
      (comparisonIso p.len).inv =
        ((comparisonIso m.len).hom ≫
          enrichedDaggerSimplexInclusion.map f ≫
          (comparisonIso n.len).inv) ≫
        ((comparisonIso n.len).hom ≫
          enrichedDaggerSimplexInclusion.map g ≫
          (comparisonIso p.len).inv)
    rw [Functor.map_comp]
    simp [Category.assoc]

instance : pathToActual.Full where
  map_surjective := by
    intro m n f
    exact (actualHomEquiv m n).surjective f

instance : pathToActual.Faithful where
  map_injective := by
    intro m n f g h
    exact (actualHomEquiv m n).injective h

instance : pathToActual.EssSurj :=
  Functor.essSurj_of_surj (by
    intro ⟨n⟩
    exact ⟨⟨n⟩, by rfl⟩)

instance : pathToActual.IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- An equivalence between the explicit path model and the exact index of
actual Part I free dagger simplicial categories. -/
def pathEquivalence : DaggerSimplex ≌ ActualDaggerSimplex :=
  pathToActual.asEquivalence

/-- The exact change-of-index functor of Part II. -/
def actualU : DaggerModels.ReverseSimplex ⥤ ActualDaggerSimplex :=
  DaggerModelsPartII.DaggerSimplexIndex.u ⋙ pathToActual

/-- On every ordinal map, the actual enriched dagger functor is the explicit
path substitution functor transported across the canonical comparison isomorphisms. -/
theorem actualU_map_conjugation {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) :
    actualU.map f = (comparisonIso m.len).hom ≫
      enrichedDaggerSimplexInclusion.map
        (DaggerModelsPartII.DaggerSimplexIndex.u.map f) ≫
      (comparisonIso n.len).inv := rfl

/-- The manuscript change-of-index functor is bijective on objects. -/
theorem actualU_obj_bijective : Function.Bijective actualU.obj := by
  constructor
  · intro m n h
    apply DaggerModelsPartII.DaggerSimplexIndex.u_obj_bijective.1
    cases m with
    | mk m =>
      cases n with
      | mk n =>
        have hlen : m = n := congrArg ActualDaggerSimplex.len h
        cases hlen
        rfl
  · intro ⟨n⟩
    exact ⟨⟨n⟩, rfl⟩

/-- The manuscript change-of-index functor is faithful. -/
instance actualU_faithful : actualU.Faithful where
  map_injective := by
    intro m n f g h
    apply DaggerModelsPartII.DaggerSimplexIndex.u_map_injective m n
    exact (pathToActual.map_injective h)

end

end DaggerModels.PartII.DaggerSimplexPartIIndex
