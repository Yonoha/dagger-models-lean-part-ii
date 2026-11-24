import OrdinaryCSSLocalization
import DaggerModelsPartII.DiagramMappingSpace
import NativeBisimplicialHorizontalMapping

/-!
# Mapping out of an ordinary horizontally discrete simplicial set

An `n`-simplex of `diagramMappingSpace (discrete.obj K) W` is a natural
transformation `discrete K × Δ[n] ⟶ W`. Evaluation at the identity simplex
of `Δ[n]` gives a horizontal map `K ⟶ W.flip.obj (op n)`. Its inverse
extends along each simplex operator into `n`. This retains the actual CSS
discrete object and the native horizontal mapping simplicial set.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels.PartII

namespace DaggerModels.PartII.OrdinaryDiscreteMapping

noncomputable section

private abbrev discrete (K : SSet.{0}) := OrdinaryCSSLocalization.discrete.obj K

/-- Evaluate a diagram-map simplex at the identity of its vertical
representable. -/
def toHorizontal (K : SSet.{0}) (W : OrdinaryCSSLocalization.Space)
    (n : SimplexCategory)
    (η : (diagramMappingSpace (discrete K) W).obj (op n)) :
    K ⟶ W.flip.obj (op n) where
  app m x := (η.app m).app (op n)
    (x, SSet.stdSimplex.objEquiv.symm (𝟙 n))
  naturality {m l} f := by
    funext x
    have h := congrFun
      (congrArg (fun t ↦ t.app (op n)) (η.naturality f))
      (x, SSet.stdSimplex.objEquiv.symm (𝟙 n))
    simpa [diagramMappingSpace, diagramTensor, discrete,
      OrdinaryCSSLocalization.discrete] using h

/-- Extend a horizontal map along the simplex operator represented by
each point of the vertical standard simplex. -/
def fromHorizontal (K : SSet.{0}) (W : OrdinaryCSSLocalization.Space)
    (n : SimplexCategory) (g : K ⟶ W.flip.obj (op n)) :
    (diagramTensor (discrete K)).obj (SSet.stdSimplex.obj n) ⟶ W where
  app m := {
    app q p := (W.obj m).map (SSet.stdSimplex.objEquiv p.2).op
      (g.app m p.1)
    naturality := by
      intro q r α
      funext p
      simp [diagramTensor, discrete, OrdinaryCSSLocalization.discrete,
        SSet.stdSimplex.map_apply]
  }
  naturality := by
    intro m l f
    apply NatTrans.ext
    funext q p
    have h := congrFun (g.naturality f) p.1
    change (W.obj l).map (SSet.stdSimplex.objEquiv p.2).op
        (g.app l (K.map f p.1)) =
      (W.map f).app q
        ((W.obj m).map (SSet.stdSimplex.objEquiv p.2).op (g.app m p.1))
    exact (congrArg
      ((W.obj l).map (SSet.stdSimplex.objEquiv p.2).op) h).trans
      (congrFun ((W.map f).naturality
        (SSet.stdSimplex.objEquiv p.2).op) (g.app m p.1)).symm

private theorem toHorizontal_fromHorizontal (K : SSet.{0})
    (W : OrdinaryCSSLocalization.Space) (n : SimplexCategory)
    (g : K ⟶ W.flip.obj (op n)) :
    toHorizontal K W n (fromHorizontal K W n g) = g := by
  apply NatTrans.ext
  funext m x
  simp [toHorizontal, fromHorizontal, SSet.stdSimplex.objEquiv]

private theorem fromHorizontal_toHorizontal (K : SSet.{0})
    (W : OrdinaryCSSLocalization.Space) (n : SimplexCategory)
    (η : (diagramMappingSpace (discrete K) W).obj (op n)) :
    fromHorizontal K W n (toHorizontal K W n η) = η := by
  apply NatTrans.ext
  funext m
  apply NatTrans.ext
  funext q p
  have h := congrFun
    ((η.app m).naturality (SSet.stdSimplex.objEquiv p.2).op)
    (p.1, SSet.stdSimplex.objEquiv.symm (𝟙 n))
  have hp :
      (((diagramTensor (discrete K)).obj (SSet.stdSimplex.obj n)).obj m).map
          (SSet.stdSimplex.objEquiv p.2).op
          (p.1, SSet.stdSimplex.objEquiv.symm (𝟙 n)) = p := by
    rcases p with ⟨x, β⟩
    change (x, SSet.stdSimplex.objEquiv.symm
      (SSet.stdSimplex.objEquiv β ≫ 𝟙 n)) = (x, β)
    simp
  change (η.app m).app q
      ((((diagramTensor (discrete K)).obj (SSet.stdSimplex.obj n)).obj m).map
        (SSet.stdSimplex.objEquiv p.2).op
        (p.1, SSet.stdSimplex.objEquiv.symm (𝟙 n))) =
    (W.obj m).map (SSet.stdSimplex.objEquiv p.2).op
      ((η.app m).app (op n)
        (p.1, SSet.stdSimplex.objEquiv.symm (𝟙 n))) at h
  rw [hp] at h
  simpa only [toHorizontal, fromHorizontal] using h.symm

/-- The levelwise bijection between CSS diagram-map simplices and native
horizontal-map simplices. -/
def levelEquiv (K : SSet.{0}) (W : OrdinaryCSSLocalization.Space)
    (n : SimplexCategory) :
    (diagramMappingSpace (discrete K) W).obj (op n) ≃
      (DaggerNativeBisimplicialHorizontalMapping.horizontalMapping K W).obj (op n) where
  toFun := toHorizontal K W n
  invFun := fromHorizontal K W n
  left_inv := fromHorizontal_toHorizontal K W n
  right_inv := toHorizontal_fromHorizontal K W n

/-- The equivalence is natural in the vertical simplex operator. -/
private theorem levelEquiv_natural (K : SSet.{0})
    (W : OrdinaryCSSLocalization.Space) {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) :
    (diagramMappingSpace (discrete K) W).map f ≫
        (levelEquiv K W m.unop).toIso.hom =
      (levelEquiv K W n.unop).toIso.hom ≫
        (DaggerNativeBisimplicialHorizontalMapping.horizontalMapping K W).map f := by
  funext η
  apply NatTrans.ext
  funext q x
  have h := congrFun
    ((η.app q).naturality f)
    (x, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))
  simpa [levelEquiv, toHorizontal, diagramMappingSpace, diagramTensor,
    discrete, OrdinaryCSSLocalization.discrete, SSet.stdSimplex.map_apply] using h

/-- The actual CSS diagram mapping space from a discrete object is the
native horizontal mapping simplicial set, at every vertical degree. -/
def mappingIso (K : SSet.{0}) (W : OrdinaryCSSLocalization.Space) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj K) W ≅
      DaggerNativeBisimplicialHorizontalMapping.horizontalMapping K W :=
  NatIso.ofComponents (fun n ↦ (levelEquiv K W n.unop).toIso)
    (by intro n m f; exact levelEquiv_natural K W f)

/-- The identification respects precomposition by every simplicial-set
map in the original horizontal variable. -/
theorem mappingIso_natural {K L : SSet.{0}} (f : K ⟶ L)
    (W : OrdinaryCSSLocalization.Space) :
    diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map f) W ≫
        (mappingIso K W).hom =
      (mappingIso L W).hom ≫
        DaggerNativeBisimplicialHorizontalMapping.horizontalPre f W := by
  apply NatTrans.ext
  funext n η
  apply NatTrans.ext
  funext q x
  rfl

#print axioms mappingIso
#print axioms mappingIso_natural

end
end DaggerModels.PartII.OrdinaryDiscreteMapping
