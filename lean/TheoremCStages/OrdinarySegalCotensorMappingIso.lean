import OrdinarySegalHorizontalCotensor
import OrdinaryDiscreteMapping
import NativeEndomorphismSimplexMaps

/-!
# The strict horizontal cotensor and discrete mapping space

The original diagram mapping space out of a horizontal discrete object
commutes with the exact horizontal cotensor. The intermediate comparison
uses the already checked discrete mapping isomorphism and the ordinary
closed tensor adjunction for simplicial sets. No fibrancy hypothesis occurs.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerNativeBisimplicialHorizontalMapping

namespace DaggerModels.PartII.OrdinarySegalCotensorMappingIso

noncomputable section

private abbrev Space := OrdinaryCSSLocalization.Space
private abbrev cotensor := OrdinarySegalHorizontalCotensor.cotensor
private abbrev discrete := OrdinaryCSSLocalization.discrete

/-- At a fixed vertical simplex, evaluation at the identity horizontal
simplex followed by the original closed adjunction. -/
private def rowLevelEquiv (K : SSet.{0}) (W : Space)
    (q : SimplexCategoryᵒᵖ) (m : SimplexCategory) :
    ((cotensor K W).flip.obj q).obj (op m) ≃
      ((ihom K).obj (W.flip.obj q)).obj (op m) :=
  (OrdinaryDiscreteMapping.levelEquiv
      (K ⊗ SSet.stdSimplex.obj m) W q.unop).trans
    (((ihom.adjunction K).homEquiv (SSet.stdSimplex.obj m)
      (W.flip.obj q)).trans SSet.yonedaEquiv)

private theorem rowLevelEquiv_pre (K : SSet.{0}) (W : Space)
    (q : SimplexCategoryᵒᵖ) {m n : SimplexCategory} (θ : m ⟶ n)
    (s : ((cotensor K W).flip.obj q).obj (op n)) :
    (OrdinaryDiscreteMapping.levelEquiv
      (K ⊗ SSet.stdSimplex.obj m) W q.unop)
        (((cotensor K W).flip.obj q).map θ.op s) =
      (K ◁ SSet.stdSimplex.map θ) ≫
        (OrdinaryDiscreteMapping.levelEquiv
          (K ⊗ SSet.stdSimplex.obj n) W q.unop) s := by
  have h := congrFun (NatTrans.congr_app
    (OrdinaryDiscreteMapping.mappingIso_natural
      (K ◁ SSet.stdSimplex.map θ) W) q) s
  simpa only [OrdinarySegalHorizontalCotensor.cotensor_map,
    OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre,
    Equiv.coe_fn_mk] using h

private theorem rowLevelEquiv_post (K : SSet.{0}) (W : Space)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    (m : SimplexCategory)
    (s : ((cotensor K W).flip.obj q).obj (op m)) :
    (OrdinaryDiscreteMapping.levelEquiv
      (K ⊗ SSet.stdSimplex.obj m) W r.unop)
        (((cotensor K W).flip.map f).app (op m) s) =
      (OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ SSet.stdSimplex.obj m) W q.unop) s ≫ W.flip.map f := by
  have h := congrFun
    ((OrdinaryDiscreteMapping.mappingIso
      (K ⊗ SSet.stdSimplex.obj m) W).hom.naturality f) s
  simpa only [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalMapping,
    Functor.comp_map, types_comp_apply] using h

/-- The actual horizontal row of the cotensor is the simplicial internal
Hom in the original horizontal row of `W`. -/
def rowIso (K : SSet.{0}) (W : Space) (q : SimplexCategoryᵒᵖ) :
    (cotensor K W).flip.obj q ≅ (ihom K).obj (W.flip.obj q) :=
  NatIso.ofComponents
    (fun m ↦ (rowLevelEquiv K W q m.unop).toIso) (by
      intro m n f
      funext s
      apply SSet.yonedaEquiv.symm.injective
      change curry ((OrdinaryDiscreteMapping.levelEquiv
          (K ⊗ SSet.stdSimplex.obj n.unop) W q.unop)
          (((cotensor K W).flip.obj q).map f s)) =
        SSet.stdSimplex.map f.unop ≫ curry ((OrdinaryDiscreteMapping.levelEquiv
          (K ⊗ SSet.stdSimplex.obj m.unop) W q.unop) s)
      rw [← curry_natural_left]
      exact congrArg curry (rowLevelEquiv_pre K W q f.unop s))

/-- The row comparison respects the original vertical operators. -/
theorem rowIso_natural (K : SSet.{0}) (W : Space)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    (cotensor K W).flip.map f ≫ (rowIso K W r).hom =
      (rowIso K W q).hom ≫ (ihom K).map (W.flip.map f) := by
  apply NatTrans.ext
  funext m s
  apply SSet.yonedaEquiv.symm.injective
  change curry ((OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ SSet.stdSimplex.obj m.unop) W r.unop)
        (((cotensor K W).flip.map f).app m s)) =
    curry ((OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ SSet.stdSimplex.obj m.unop) W q.unop) s) ≫
      (ihom K).map (W.flip.map f)
  calc
    curry ((OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ SSet.stdSimplex.obj m.unop) W r.unop)
        (((cotensor K W).flip.map f).app m s)) =
      curry ((OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ SSet.stdSimplex.obj m.unop) W q.unop) s ≫ W.flip.map f) :=
          congrArg curry (rowLevelEquiv_post K W f m.unop s)
    _ = _ := curry_natural_right _ _

/-- The full vertical diagram version of the row isomorphism. -/
def rowFamilyIso (K : SSet.{0}) (W : Space) :
    (cotensor K W).flip ≅ W.flip ⋙ ihom K :=
  NatIso.ofComponents (fun q ↦ rowIso K W q) (by
    intro q r f
    exact rowIso_natural K W f)

/-- Closed currying, applied pointwise to the original vertical diagram. -/
def closedMappingIso (K A : SSet.{0}) (W : Space) :
    (W.flip ⋙ ihom K) ⋙ coyoneda.obj (op A) ≅
      horizontalMapping (K ⊗ A) W :=
  NatIso.ofComponents
    (fun q ↦ (((ihom.adjunction K).homEquiv A
      (W.flip.obj q)).symm).toIso) (by
      intro q r f
      funext g
      change uncurry (g ≫ (ihom K).map (W.flip.map f)) =
        uncurry g ≫ W.flip.map f
      exact uncurry_natural_right g (W.flip.map f))

/-- Strict Fubini isomorphism for the original CSS diagram mapping space
and the literal horizontal cotensor. -/
def mappingIso (K A : SSet.{0}) (W : Space) :
    diagramMappingSpace (discrete.obj A) (cotensor K W) ≅
      diagramMappingSpace (discrete.obj (K ⊗ A)) W :=
  OrdinaryDiscreteMapping.mappingIso A (cotensor K W) ≪≫
    Functor.isoWhiskerRight (rowFamilyIso K W) (coyoneda.obj (op A)) ≪≫
      closedMappingIso K A W ≪≫
        (OrdinaryDiscreteMapping.mappingIso (K ⊗ A) W).symm

private theorem discreteLevel_pre {A B : SSet.{0}} (f : A ⟶ B)
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

/-- Fubini respects every original horizontal source map. -/
theorem mappingIso_natural_source (K : SSet.{0})
    {A B : SSet.{0}} (f : A ⟶ B) (W : Space) :
    diagramMappingPrecomp (discrete.map f) (cotensor K W) ≫
        (mappingIso K A W).hom =
      (mappingIso K B W).hom ≫
        diagramMappingPrecomp (discrete.map (K ◁ f)) W := by
  apply NatTrans.ext
  funext q t
  apply (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop).injective
  change (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
      ((mappingIso K A W).hom.app q
        ((diagramMappingPrecomp (discrete.map f) (cotensor K W)).app q t)) =
    (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
      ((diagramMappingPrecomp (discrete.map (K ◁ f)) W).app q
        ((mappingIso K B W).hom.app q t))
  rw [mappingIso_app, discreteLevel_pre, discreteLevel_pre, mappingIso_app]
  rw [Category.assoc]
  exact uncurry_natural_left f _

#print axioms rowIso
#print axioms rowIso_natural
#print axioms rowFamilyIso
#print axioms closedMappingIso
#print axioms mappingIso
#print axioms mappingIso_natural_source

end
end DaggerModels.PartII.OrdinarySegalCotensorMappingIso
