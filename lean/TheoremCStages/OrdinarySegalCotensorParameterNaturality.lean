import OrdinarySegalCotensorMappingIso
import OrdinarySegalHorizontalCotensor

/-!
# Naturality of strict Fubini in the cotensor parameter

The checked Fubini isomorphism is natural in its horizontal source. This
file proves its remaining contravariant naturality in the cotensor
parameter. Both statements use the exact original horizontal cotensor.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed

namespace DaggerModels.PartII.OrdinarySegalCotensorParameterNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalCotensorMappingIso (rowIso mappingIso)

noncomputable section

private theorem level_pre {A B : SSet.{0}} (f : A ⟶ B)
    (W : Space) (q : SimplexCategoryᵒᵖ)
    (t : (diagramMappingSpace (discrete.obj B) W).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv A W q.unop)
        ((diagramMappingPrecomp (discrete.map f) W).app q t) =
      f ≫ (OrdinaryDiscreteMapping.levelEquiv B W q.unop) t := by
  have h := congrFun
    (NatTrans.congr_app (OrdinaryDiscreteMapping.mappingIso_natural f W) q) t
  simpa only [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre,
    Equiv.coe_fn_mk] using h

private theorem level_post (A : SSet.{0}) {W V : Space}
    (g : W ⟶ V) (q : SimplexCategoryᵒᵖ)
    (t : (diagramMappingSpace (discrete.obj A) W).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv A V q.unop)
        ((diagramMappingPostcomp (discrete.obj A) g).app q t) =
      (OrdinaryDiscreteMapping.levelEquiv A W q.unop) t ≫
        ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map g).app q := by
  apply NatTrans.ext
  funext m x
  rfl

/-- At every original vertical simplex, the row isomorphism commutes with
parameter precomposition by the exact map `f`. -/
theorem rowIso_natural_parameter {K L : SSet.{0}} (f : K ⟶ L)
    (W : Space) (q : SimplexCategoryᵒᵖ) :
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
        (pre f W)).app q ≫ (rowIso K W q).hom =
      (rowIso L W q).hom ≫ (MonoidalClosed.pre f).app (W.flip.obj q) := by
  apply NatTrans.ext
  funext m s
  apply SSet.yonedaEquiv.symm.injective
  change curry ((OrdinaryDiscreteMapping.levelEquiv
      (K ⊗ SSet.stdSimplex.obj m.unop) W q.unop)
        (((pre f W).app (op m.unop)).app q s)) =
    curry ((OrdinaryDiscreteMapping.levelEquiv
      (L ⊗ SSet.stdSimplex.obj m.unop) W q.unop) s) ≫
        (MonoidalClosed.pre f).app (W.flip.obj q)
  rw [curry_pre_app, OrdinarySegalHorizontalCotensor.pre_app]
  exact congrArg curry (level_pre (f ▷ SSet.stdSimplex.obj m.unop) W q s)

private theorem mappingIso_app (K A : SSet.{0}) (W : Space)
    (q : SimplexCategoryᵒᵖ)
    (t : (diagramMappingSpace (discrete.obj A) (cotensor K W)).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
        ((mappingIso K A W).hom.app q t) =
      uncurry ((OrdinaryDiscreteMapping.levelEquiv A (cotensor K W) q.unop) t ≫
        (rowIso K W q).hom) := by
  change (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
      ((OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop).symm
        (uncurry ((OrdinaryDiscreteMapping.levelEquiv A (cotensor K W) q.unop) t ≫
          (rowIso K W q).hom))) = _
  exact Equiv.apply_symm_apply
    (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
    (uncurry ((OrdinaryDiscreteMapping.levelEquiv A (cotensor K W) q.unop) t ≫
      (rowIso K W q).hom))

/-- Strict Fubini commutes with parameter precomposition. The right hand
side uses the same tensor map `f ▷ A` as the original cotensor. -/
theorem mappingIso_natural_parameter {K L : SSet.{0}} (f : K ⟶ L)
    (A : SSet.{0}) (W : Space) :
    diagramMappingPostcomp (discrete.obj A)
      (W := cotensor L W) (W' := cotensor K W) (pre f W) ≫
        (mappingIso K A W).hom =
      (mappingIso L A W).hom ≫
        diagramMappingPrecomp (discrete.map (f ▷ A)) W := by
  apply NatTrans.ext
  funext q t
  apply (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop).injective
  change (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
      ((mappingIso K A W).hom.app q
        ((diagramMappingPostcomp (discrete.obj A)
      (W := cotensor L W) (W' := cotensor K W) (pre f W)).app q t)) =
    (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
      ((diagramMappingPrecomp (discrete.map (f ▷ A)) W).app q
        ((mappingIso L A W).hom.app q t))
  rw [mappingIso_app, level_post, level_pre, mappingIso_app]
  let z := (OrdinaryDiscreteMapping.levelEquiv A (cotensor L W) q.unop) t
  let r := ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
    (pre f W)).app q
  have h := congrArg (fun g ↦ z ≫ g) (rowIso_natural_parameter f W q)
  have h' : (z ≫ r) ≫ (rowIso K W q).hom =
      (z ≫ (rowIso L W q).hom) ≫ (MonoidalClosed.pre f).app (W.flip.obj q) := by
    simpa only [Category.assoc] using h
  exact (congrArg uncurry h').trans
    (uncurry_pre_app (W.flip.obj q) (z ≫ (rowIso L W q).hom) f)

#print axioms rowIso_natural_parameter
#print axioms mappingIso_natural_parameter

end
end DaggerModels.PartII.OrdinarySegalCotensorParameterNaturality
