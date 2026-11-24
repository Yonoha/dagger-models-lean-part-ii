import OrdinaryJTCurriedAdjunction
import OrdinaryJTColumnOperators
import OrdinaryJTMappingFrameWeak
import NativeBisimplicialHorizontalMapping

/-!
# Horizontal mapping into the actual ordinary JT right nerve

At vertical degree `n`, a horizontal map from `K` to the original curried
restricted-Yoneda nerve is a coherent family of maps
`Δ[m] × J[n] ⟶ X`. Evaluation at each identity horizontal simplex gives
one map `K × J[n] ⟶ X`. Conversely a map from that unchanged tensor
weight extends along every represented horizontal simplex operator.
The two constructions commute with horizontal restriction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MonoidalCategory
open DaggerModels DaggerNativeBisimplicialHorizontalMapping

namespace DaggerModels.PartII.OrdinaryJTHorizontalMapping

noncomputable section

open OrdinaryJTColumnOperators

private abbrev J (n : SimplexCategory) := GroupoidSimplex.parameter.obj n
private abbrev R (X : SSet.{0}) := OrdinaryJTCurriedAdjunction.right.obj X

/-- Evaluate the full native horizontal map at the identity of its
representing horizontal simplex. -/
def toFrame (K X : SSet.{0}) (n : SimplexCategory)
    (g : (horizontalMapping K (R X)).obj (op n)) :
    (OrdinaryJTMappingFrameWeak.frame K).obj n ⟶ X where
  app q p := (g.app q p.1).down.app q
    (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop), p.2)
  naturality := by
    intro q r α
    funext p
    have hg := congrFun (g.naturality α) p.1
    have hg' := congrArg
      (fun z : ((R X).flip.obj (op n)).obj r ↦
        z.down.app r (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop),
          (J n).map α p.2)) hg
    have hc := column_horizontal_map_down X n α (g.app q p.1)
    have hc' := congrArg
      (fun t : SSet.stdSimplex.obj r.unop ⊗ J n ⟶ X ↦
        t.app r (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop),
          (J n).map α p.2)) hc
    have hz := congrFun ((g.app q p.1).down.naturality α)
      (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop), p.2)
    change (g.app r (K.map α p.1)).down.app r
        (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop), (J n).map α p.2) =
      X.map α ((g.app q p.1).down.app q
        (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop), p.2))
    exact hg'.trans (hc'.trans (by
      simpa [OrdinaryJTMappingFrameWeak.frame,
        SSet.stdSimplex.map_apply] using hz))

/-- Extend a map on the unchanged `K × J[n]` weight along each
horizontal simplex operator. -/
def fromFrame (K X : SSet.{0}) (n : SimplexCategory)
    (h : (OrdinaryJTMappingFrameWeak.frame K).obj n ⟶ X) :
    (horizontalMapping K (R X)).obj (op n) where
  app q x := ULift.up {
    app := fun r p ↦ h.app r
      (K.map (SSet.stdSimplex.objEquiv p.1).op x, p.2)
    naturality := by
      intro r s α
      funext p
      have hh := congrFun (h.naturality α)
        (K.map (SSet.stdSimplex.objEquiv p.1).op x, p.2)
      simpa [OrdinaryJTMappingFrameWeak.frame,
        SSet.stdSimplex.map_apply, K.map_comp] using hh }
  naturality := by
    intro q r α
    funext x
    apply ULift.ext
    apply NatTrans.ext
    funext s p
    change _ = (((R X).flip.obj (op n)).map α _).down.app s p
    rw [column_horizontal_map_down]
    change h.app s (K.map (SSet.stdSimplex.objEquiv p.1).op (K.map α x), p.2) =
      h.app s (K.map (SSet.stdSimplex.objEquiv
        ((SSet.stdSimplex.map α.unop).app s p.1)).op x, p.2)
    have hβ : SSet.stdSimplex.objEquiv
        ((SSet.stdSimplex.map α.unop).app s p.1) =
          SSet.stdSimplex.objEquiv p.1 ≫ α.unop := by
      have he := congrArg SSet.stdSimplex.objEquiv
        (SSet.stdSimplex.objEquiv_symm_comp (SSet.stdSimplex.objEquiv p.1) α.unop)
      simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using he.symm
    rw [hβ, op_comp, K.map_comp]
    simp only [Quiver.Hom.op_unop, types_comp_apply]

private theorem toFrame_fromFrame (K X : SSet.{0}) (n : SimplexCategory)
    (h : (OrdinaryJTMappingFrameWeak.frame K).obj n ⟶ X) :
    toFrame K X n (fromFrame K X n h) = h := by
  apply NatTrans.ext
  funext q p
  simp [toFrame, fromFrame]

private theorem fromFrame_toFrame (K X : SSet.{0}) (n : SimplexCategory)
    (g : (horizontalMapping K (R X)).obj (op n)) :
    fromFrame K X n (toFrame K X n g) = g := by
  apply NatTrans.ext
  funext q x
  apply ULift.ext
  apply NatTrans.ext
  funext r p
  have hg := congrFun (g.naturality (SSet.stdSimplex.objEquiv p.1).op) x
  have hg' := congrArg
    (fun z : ((R X).flip.obj (op n)).obj r ↦
      z.down.app r (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop), p.2)) hg
  change (g.app r (K.map (SSet.stdSimplex.objEquiv p.1).op x)).down.app r
      (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop), p.2) =
    (((R X).flip.obj (op n)).map (SSet.stdSimplex.objEquiv p.1).op
      (g.app q x)).down.app r
        (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop), p.2) at hg'
  rw [column_horizontal_map_down] at hg'
  have hβ : (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv p.1)).app r
      (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop)) = p.1 := by
    rw [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp,
      Equiv.symm_apply_apply]
  change (g.app r (K.map (SSet.stdSimplex.objEquiv p.1).op x)).down.app r
      (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop), p.2) =
    (g.app q x).down.app r
      ((SSet.stdSimplex.map (SSet.stdSimplex.objEquiv p.1)).app r
        (SSet.stdSimplex.objEquiv.symm (𝟙 r.unop)), p.2) at hg'
  rw [hβ] at hg'
  simpa [toFrame, fromFrame] using hg'

/-- Each vertical degree has the original full tensor-frame Hom set. -/
def levelEquiv (K X : SSet.{0}) (n : SimplexCategory) :
    (horizontalMapping K (R X)).obj (op n) ≃
      (OrdinaryJTMappingFrameWeak.mapping X K).obj (op n) where
  toFun := toFrame K X n
  invFun := fromFrame K X n
  left_inv := fromFrame_toFrame K X n
  right_inv := toFrame_fromFrame K X n

private theorem levelEquiv_natural (K X : SSet.{0})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (horizontalMapping K (R X)).map f ≫ (levelEquiv K X m.unop).toIso.hom =
      (levelEquiv K X n.unop).toIso.hom ≫
        (OrdinaryJTMappingFrameWeak.mapping X K).map f := by
  funext g
  apply NatTrans.ext
  funext q p
  rfl

/-- The native horizontal mapping simplicial set of the original right
nerve is exactly the existing ordinary JT mapping-frame simplicial set. -/
def mappingIso (K X : SSet.{0}) :
    horizontalMapping K (OrdinaryJTCurriedAdjunction.right.obj X) ≅
      OrdinaryJTMappingFrameWeak.mapping X K :=
  NatIso.ofComponents (fun n ↦ (levelEquiv K X n.unop).toIso)
    (by intro n m f; exact levelEquiv_natural K X f)

/-- The comparison respects every original horizontal source map. -/
theorem mappingIso_natural_source {K L : SSet.{0}} (u : K ⟶ L)
    (X : SSet.{0}) :
    horizontalPre u (R X) ≫ (mappingIso K X).hom =
      (mappingIso L X).hom ≫ OrdinaryJTMappingFrameWeak.restriction X u := by
  apply NatTrans.ext
  funext n g
  apply NatTrans.ext
  funext q p
  rfl

#print axioms mappingIso
#print axioms mappingIso_natural_source

end
end DaggerModels.PartII.OrdinaryJTHorizontalMapping
