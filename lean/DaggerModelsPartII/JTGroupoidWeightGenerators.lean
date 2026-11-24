import DaggerModelsPartII.JTGroupoidWeightWeak
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Generators and relations for the scalar completed-simplex realization

The generator of the actual left Kan extension `jRealization` is a leg of its
pointwise simplex cocone. Every simplex comes from one leg. Compatible legs
descend to a unique map by the same cocone's colimit universal property.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTGroupoidWeightGenerators

open JTGroupoidWeightWeak GroupoidSimplex

noncomputable section

/-- The native left Kan extension unit for the literal completed-simplex
parameter. -/
def unit : GroupoidSimplex.parameter ⟶ uliftYoneda.{0} ⋙ jRealization :=
  uliftYoneda.{0}.leftKanExtensionUnit GroupoidSimplex.parameter

private instance isLeftKanExtension : jRealization.IsLeftKanExtension unit := by
  dsimp [jRealization, unit]
  infer_instance

/-- The actual simplex category and diagram for the scalar weight. -/
abbrev SimplexIndex (K : SSet.{0}) := CostructuredArrow uliftYoneda.{0} K

def simplexDiagram (K : SSet.{0}) : SimplexIndex K ⥤ SSet.{0} :=
  CostructuredArrow.proj uliftYoneda K ⋙ GroupoidSimplex.parameter

/-- The pointwise left Kan extension cocone at the given scalar input. -/
def simplexCocone (K : SSet.{0}) : Cocone (simplexDiagram K) :=
  (Functor.LeftExtension.mk jRealization unit).coconeAt K

theorem simplexCocone_leg (K : SSet.{0}) (σ : SimplexIndex K) :
    (simplexCocone K).ι.app σ =
      unit.app σ.left ≫ jRealization.map σ.hom := rfl

/-- The native pointwise colimit property of the same simplex cocone. -/
def simplexCoconeIsColimit (K : SSet.{0}) : IsColimit (simplexCocone K) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension jRealization unit K

/-- Evaluation at a vertical test degree preserves the actual simplex
colimit. This is the Type-valued universal property used when a proposed
leg is a function of the test-degree simplices rather than an SSet map. -/
def simplexCoconeAtIsColimit (K : SSet.{0}) (q : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type)).obj q).mapCocone
      (simplexCocone K)) :=
  isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type)).obj q)
    (simplexCoconeIsColimit K)

/-- The canonical coend generator specified by a vertical simplex and a
presheaf element. -/
def generator (K : SSet.{0}) (k : SimplexCategory) (w : K.obj (op k)) :
    GroupoidSimplex.parameter.obj k ⟶ jRealization.obj K :=
  unit.app k ≫ jRealization.map (uliftYonedaEquiv.{0}.symm w)

theorem generator_eq_cocone (K : SSet.{0}) (k : SimplexCategory)
    (w : K.obj (op k)) :
    generator K k w =
      (simplexCocone K).ι.app
        (CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w)) := rfl

/-- The literal coend relation for a vertical simplex operator. -/
theorem generator_relation (K : SSet.{0}) {k l : SimplexCategory}
    (f : k ⟶ l) (w : K.obj (op l)) :
    GroupoidSimplex.parameter.map f ≫ generator K l w =
      generator K k (K.map f.op w) := by
  change GroupoidSimplex.parameter.map f ≫
      (unit.app l ≫ jRealization.map (uliftYonedaEquiv.{0}.symm w)) =
    unit.app k ≫ jRealization.map (uliftYonedaEquiv.{0}.symm (K.map f.op w))
  rw [← Category.assoc, unit.naturality f, Category.assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  exact congrArg (fun h ↦ unit.app k ≫ jRealization.map h)
    (uliftYonedaEquiv_symm_map f.op w).symm

/-- Naturality in the actual scalar simplicial-set input. -/
theorem generator_naturality {K L : SSet.{0}} (g : K ⟶ L)
    (k : SimplexCategory) (w : K.obj (op k)) :
    generator K k w ≫ jRealization.map g =
      generator L k (g.app (op k) w) := by
  dsimp [generator]
  rw [Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg jRealization.map
  apply uliftYonedaEquiv.{0}.injective
  rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Every simplex of the scalar realization comes from a generator. -/
theorem exists_generator (K : SSet.{0}) (q : SimplexCategoryᵒᵖ)
    (x : (jRealization.obj K).obj q) :
    ∃ (k : SimplexCategory) (w : K.obj (op k))
      (ξ : (GroupoidSimplex.parameter.obj k).obj q),
      (generator K k w).app q ξ = x := by
  let E : SSet.{0} ⥤ Type := (evaluation _ _).obj q
  obtain ⟨σ, ξ, hξ⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves E (simplexCoconeIsColimit K)) x
  refine ⟨σ.left, uliftYonedaEquiv.{0} σ.hom, ξ, ?_⟩
  simpa only [generator, Equiv.symm_apply_apply] using hξ

/-- Maps out of the realization are determined on all literal generators. -/
theorem hom_ext {K Y : SSet.{0}} {f g : jRealization.obj K ⟶ Y}
    (h : ∀ (k : SimplexCategory) (w : K.obj (op k)),
      generator K k w ≫ f = generator K k w ≫ g) : f = g := by
  ext q x
  obtain ⟨k, w, ξ, hξ⟩ := exists_generator K q x
  rw [← hξ]
  exact congrFun (NatTrans.congr_app (h k w) q) ξ

/-- Compatible generator legs, in the exact vertical operator direction. -/
def Compatible (K Y : SSet.{0})
    (leg : ∀ (k : SimplexCategory) (_ : K.obj (op k)),
      GroupoidSimplex.parameter.obj k ⟶ Y) : Prop :=
  ∀ {k l : SimplexCategory} (f : k ⟶ l) (w : K.obj (op l)),
    GroupoidSimplex.parameter.map f ≫ leg l w = leg k (K.map f.op w)

/-- The cocone specified by compatible generator legs. -/
def coconeOfCompatible {K Y : SSet.{0}}
    (leg : ∀ (k : SimplexCategory) (_ : K.obj (op k)),
      GroupoidSimplex.parameter.obj k ⟶ Y)
    (hleg : Compatible K Y leg) : Cocone (simplexDiagram K) where
  pt := Y
  ι :=
    { app σ := leg σ.left (uliftYonedaEquiv.{0} σ.hom)
      naturality := by
        intro σ τ f
        change GroupoidSimplex.parameter.map f.left ≫
          leg τ.left (uliftYonedaEquiv.{0} τ.hom) =
            leg σ.left (uliftYonedaEquiv.{0} σ.hom)
        rw [hleg f.left (uliftYonedaEquiv.{0} τ.hom)]
        congr 1
        rw [uliftYonedaEquiv_naturality]
        change uliftYonedaEquiv.{0} (uliftYoneda.map f.left ≫ τ.hom) =
          uliftYonedaEquiv.{0} σ.hom
        rw [CostructuredArrow.w f]
        rfl }

/-- The actual colimit descent from compatible scalar generator legs. -/
def desc {K Y : SSet.{0}}
    (leg : ∀ (k : SimplexCategory) (_ : K.obj (op k)),
      GroupoidSimplex.parameter.obj k ⟶ Y)
    (hleg : Compatible K Y leg) : jRealization.obj K ⟶ Y :=
  (simplexCoconeIsColimit K).desc (coconeOfCompatible leg hleg)

@[reassoc] theorem generator_desc {K Y : SSet.{0}}
    (leg : ∀ (k : SimplexCategory) (_ : K.obj (op k)),
      GroupoidSimplex.parameter.obj k ⟶ Y)
    (hleg : Compatible K Y leg)
    (k : SimplexCategory) (w : K.obj (op k)) :
    generator K k w ≫ desc leg hleg = leg k w := by
  rw [generator_eq_cocone]
  simpa only [desc, coconeOfCompatible, CostructuredArrow.mk_left,
    CostructuredArrow.mk_hom_eq_self, Equiv.apply_symm_apply] using
    (simplexCoconeIsColimit K).fac (coconeOfCompatible leg hleg)
      (CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w))

/-- Uniqueness of the compatible-leg descent. -/
theorem desc_unique {K Y : SSet.{0}}
    (leg : ∀ (k : SimplexCategory) (_ : K.obj (op k)),
      GroupoidSimplex.parameter.obj k ⟶ Y)
    (hleg : Compatible K Y leg) (f : jRealization.obj K ⟶ Y)
    (hf : ∀ k w, generator K k w ≫ f = leg k w) :
    f = desc leg hleg := by
  apply hom_ext
  intro k w
  rw [hf, generator_desc]

end

end DaggerModels.PartII.JTGroupoidWeightGenerators
