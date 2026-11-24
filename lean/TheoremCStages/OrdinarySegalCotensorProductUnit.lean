import OrdinarySegalCotensorProductParameterNaturality

/-!
# Unit and constant-section coherence for cotensor association

The point-parameter cotensor and the native Cartesian right unitor
compare the checked strict product isomorphism. Naturality in the outer
parameter then gives the literal constant-section square for successive
cotensors, without a fibrancy or completeness hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed

namespace DaggerModels.PartII.OrdinarySegalCotensorProductUnit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalHorizontalCotensorPoint (pointIso constantSection)
open OrdinarySegalCotensorProductIso (productIso)

noncomputable section

private theorem level_pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space)
    (q : SimplexCategoryᵒᵖ)
    (t : (diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj L) W).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv K W q.unop)
        ((diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map f) W).app q t) =
      f ≫ (OrdinaryDiscreteMapping.levelEquiv L W q.unop) t := by
  have h := congrFun
    (NatTrans.congr_app (OrdinaryDiscreteMapping.mappingIso_natural f W) q) t
  simpa only [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre,
    Equiv.coe_fn_mk] using h

private theorem point_level (V : Space) (n : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (t : (V.obj (op n)).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv
      ((Δ[0] : SSet.{0}) ⊗ SSet.stdSimplex.obj n) V q.unop)
        (((pointIso V).inv.app (op n)).app q t) =
      (SSet.stdSimplex.leftUnitor (SSet.stdSimplex.obj n)).hom ≫
        (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm t := by
  induction n using SimplexCategory.rec with | _ d =>
    change (OrdinaryDiscreteMapping.levelEquiv
        ((Δ[0] : SSet.{0}) ⊗ (Δ[d] : SSet.{0})) V q.unop)
          ((diagramMappingPrecomp
            (OrdinaryCSSLocalization.discrete.map
              (SSet.stdSimplex.leftUnitor (Δ[d] : SSet.{0})).hom) V).app q
              ((OrdinarySegalWalkingEvaluation.simplexMappingIso V d).inv.app q t)) = _
    rw [level_pre]
    congr 1
    apply SSet.yonedaEquiv.injective
    change (OrdinarySegalWalkingEvaluation.simplexMappingIso V d).hom.app q
        ((OrdinarySegalWalkingEvaluation.simplexMappingIso V d).inv.app q t) =
      SSet.yonedaEquiv ((SSet.yonedaEquiv (X := V.flip.obj q)).symm t)
    rw [Equiv.apply_symm_apply]
    exact congrFun (NatTrans.congr_app
      (OrdinarySegalWalkingEvaluation.simplexMappingIso V d).inv_hom_id q) t

private theorem row_yoneda (B : SSet.{0}) (W : Space)
    (q : SimplexCategoryᵒᵖ) (n : SimplexCategory)
    (t : ((cotensor B W).obj (op n)).obj q) :
    (SSet.yonedaEquiv
        (X := (ihom B).obj (W.flip.obj q)) (n := n)).symm
        ((OrdinarySegalCotensorMappingIso.rowIso B W q).hom.app (op n) t) =
      curry ((OrdinaryDiscreteMapping.levelEquiv
        (B ⊗ SSet.stdSimplex.obj n) W q.unop) t) := by
  change (SSet.yonedaEquiv
      (X := (ihom B).obj (W.flip.obj q)) (n := n)).symm
      (SSet.yonedaEquiv (curry ((OrdinaryDiscreteMapping.levelEquiv
        (B ⊗ SSet.stdSimplex.obj n) W q.unop) t))) = _
  exact Equiv.symm_apply_apply _ _

private theorem fubini_level (B D : SSet.{0}) (W : Space)
    (q : SimplexCategoryᵒᵖ)
    (t : (diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj D)
      (cotensor B W)).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv (B ⊗ D) W q.unop)
        ((OrdinarySegalCotensorMappingIso.mappingIso B D W).hom.app q t) =
      uncurry ((OrdinaryDiscreteMapping.levelEquiv D (cotensor B W) q.unop) t ≫
        (OrdinarySegalCotensorMappingIso.rowIso B W q).hom) := by
  change (OrdinaryDiscreteMapping.levelEquiv (B ⊗ D) W q.unop)
      ((OrdinaryDiscreteMapping.levelEquiv (B ⊗ D) W q.unop).symm
        (uncurry ((OrdinaryDiscreteMapping.levelEquiv D (cotensor B W) q.unop) t ≫
          (OrdinarySegalCotensorMappingIso.rowIso B W q).hom))) = _
  exact Equiv.apply_symm_apply _ _

/-- The product comparison at the point parameter is the native right
unitor precomposition on the actual horizontal cotensor. -/
theorem point_product (B : SSet.{0}) (W : Space) :
    (pointIso (cotensor B W)).inv ≫
        (productIso (Δ[0] : SSet.{0}) B W).hom =
      pre (SSet.stdSimplex.rightUnitor B).hom W := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext q t
  let D := SSet.stdSimplex.obj n.unop
  let g := (OrdinaryDiscreteMapping.levelEquiv (B ⊗ D) W q.unop) t
  let A := (α_ B (Δ[0] : SSet.{0}) D).hom
  let R := (SSet.stdSimplex.rightUnitor B).hom ▷ D
  let L := (SSet.stdSimplex.leftUnitor D).hom
  have hTriangle : A ≫ B ◁ L = R := by
    apply NatTrans.ext
    funext q x
    rfl
  apply (OrdinaryDiscreteMapping.levelEquiv ((B ⊗ (Δ[0] : SSet.{0})) ⊗ D)
    W q.unop).injective
  change (OrdinaryDiscreteMapping.levelEquiv ((B ⊗ (Δ[0] : SSet.{0})) ⊗ D)
      W q.unop)
      ((diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map A) W).app q
        ((OrdinarySegalCotensorMappingIso.mappingIso B
          ((Δ[0] : SSet.{0}) ⊗ D) W).hom.app q
            (((pointIso (cotensor B W)).inv.app n).app q t))) =
    (OrdinaryDiscreteMapping.levelEquiv ((B ⊗ (Δ[0] : SSet.{0})) ⊗ D)
      W q.unop)
      ((diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map R) W).app q t)
  rw [level_pre, level_pre, fubini_level,
    point_level (cotensor B W) n.unop q t]
  calc
    A ≫ uncurry
        ((L ≫ (SSet.yonedaEquiv
          (X := (cotensor B W).flip.obj q) (n := n.unop)).symm t) ≫
          (OrdinarySegalCotensorMappingIso.rowIso B W q).hom) =
      A ≫ (B ◁ L) ≫ uncurry
        ((SSet.yonedaEquiv
          (X := (cotensor B W).flip.obj q) (n := n.unop)).symm t ≫
            (OrdinarySegalCotensorMappingIso.rowIso B W q).hom) := by
              rw [Category.assoc, uncurry_natural_left]
    _ = A ≫ (B ◁ L) ≫ g := by
      rw [SSet.yonedaEquiv_symm_comp, row_yoneda, uncurry_curry]
    _ = R ≫ g := by rw [← Category.assoc, hTriangle]

/-- The inverse form used when a whole product-parameter map is curried
to a coherent arrow in the original cotensor. -/
theorem point_product_inv (B : SSet.{0}) (W : Space) :
    (productIso (Δ[0] : SSet.{0}) B W).inv ≫
        (pointIso (cotensor B W)).hom =
      pre (SSet.stdSimplex.rightUnitor B).inv W := by
  let I : cotensor B W ≅ cotensor (B ⊗ (Δ[0] : SSet.{0})) W :=
    (pointIso (cotensor B W)).symm ≪≫
      productIso (Δ[0] : SSet.{0}) B W
  have hI : I.hom = pre (SSet.stdSimplex.rightUnitor B).hom W :=
    point_product B W
  have hInv : I.inv = pre (SSet.stdSimplex.rightUnitor B).inv W := by
    apply (cancel_epi I.hom).mp
    rw [Iso.hom_inv_id, hI, ← OrdinarySegalHorizontalCotensor.pre_comp,
      Iso.inv_hom_id, OrdinarySegalHorizontalCotensor.pre_id]
  exact hInv

/-- Successive actual constant sections equal the original constant
section for the ordered parameter product under the product isomorphism. -/
theorem constantSection_product (A B : SSet.{0}) (W : Space) :
    constantSection B W ≫ constantSection A (cotensor B W) ≫
        (productIso A B W).hom =
      constantSection (B ⊗ A) W := by
  let tA := SSet.stdSimplex.isTerminalObj₀.from A
  let tB := SSet.stdSimplex.isTerminalObj₀.from B
  have ht : (B ◁ tA) ≫ (SSet.stdSimplex.rightUnitor B).hom ≫ tB =
      SSet.stdSimplex.isTerminalObj₀.from (B ⊗ A) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  dsimp only [constantSection, OrdinarySegalHorizontalCotensor.constantMap]
  calc
    (pointIso W).inv ≫ pre tB W ≫
        ((pointIso (cotensor B W)).inv ≫ pre tA (cotensor B W)) ≫
          (productIso A B W).hom =
      (pointIso W).inv ≫ pre tB W ≫
        ((pointIso (cotensor B W)).inv ≫
          (productIso (Δ[0] : SSet.{0}) B W).hom) ≫
            pre (B ◁ tA) W := by
              simp only [Category.assoc]
              rw [
                OrdinarySegalCotensorProductParameterNaturality.productIso_natural_outer
                  B tA W]
    _ = (pointIso W).inv ≫ pre tB W ≫
          pre (SSet.stdSimplex.rightUnitor B).hom W ≫ pre (B ◁ tA) W := by
            rw [point_product]
    _ = (pointIso W).inv ≫
          pre (SSet.stdSimplex.isTerminalObj₀.from (B ⊗ A)) W := by
            rw [← OrdinarySegalHorizontalCotensor.pre_comp,
              ← OrdinarySegalHorizontalCotensor.pre_comp, Category.assoc, ht]

#print axioms point_product
#print axioms point_product_inv
#print axioms constantSection_product

end
end DaggerModels.PartII.OrdinarySegalCotensorProductUnit
