import DaggerModelsPartII.SemiSimplexBoundaryLifting
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Products

/-! Pair relative boundary lifts over the actual product of two simplicial sets. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open scoped Prod

namespace DaggerModels.PartII.SemiSimplexBoundaryLifting

noncomputable section

private abbrev inc := SemiSimplexCategory.toSimplexCategory
private abbrev restrict (X : SSet.{0}) := inc.op ⋙ X

/-- Pairs of independent choices with componentwise genuine time restriction. -/
def pairedChoices (E F : SemiSimplexCategoryᵒᵖ ⥤ Type) :
    SemiSimplexCategoryᵒᵖ ⥤ Type :=
  E.prod' F ⋙ Functor.uncurry.obj Types.binaryProductFunctor

private abbrev eval (n : SimplexCategoryᵒᵖ) := (evaluation SimplexCategoryᵒᵖ Type).obj n

private def productAt (X Y : SSet.{0}) (n : SimplexCategoryᵒᵖ) :
    (X ⨯ Y).obj n ≃ X.obj n × Y.obj n :=
  (PreservesLimitPair.iso (eval n) X Y ≪≫ Types.binaryProductIso _ _).toEquiv

private theorem productAt_fst {X Y : SSet.{0}} {n : SimplexCategoryᵒᵖ}
    (z : (X ⨯ Y).obj n) :
    (productAt X Y n z).1 = (prod.fst : X ⨯ Y ⟶ X).app n z := by
  have he : (PreservesLimitPair.iso (eval n) X Y).hom ≫ (Types.binaryProductIso _ _).hom ≫
      _root_.Prod.fst = (eval n).map (prod.fst : X ⨯ Y ⟶ X) := by
    rw [Types.binaryProductIso_hom_comp_fst, PreservesLimitPair.iso_hom, prodComparison_fst]
  exact congrFun he z

private theorem productAt_snd {X Y : SSet.{0}} {n : SimplexCategoryᵒᵖ}
    (z : (X ⨯ Y).obj n) :
    (productAt X Y n z).2 = (prod.snd : X ⨯ Y ⟶ Y).app n z := by
  have he : (PreservesLimitPair.iso (eval n) X Y).hom ≫ (Types.binaryProductIso _ _).hom ≫
      _root_.Prod.snd = (eval n).map (prod.snd : X ⨯ Y ⟶ Y) := by
    rw [Types.binaryProductIso_hom_comp_snd, PreservesLimitPair.iso_hom, prodComparison_snd]
  exact congrFun he z

private theorem productAt_map {X Y : SSet.{0}} {m n : SimplexCategoryᵒᵖ}
    (j : m ⟶ n) (z : (X ⨯ Y).obj m) :
    productAt X Y n ((X ⨯ Y).map j z) =
      (X.map j (productAt X Y m z).1, Y.map j (productAt X Y m z).2) := by
  apply Prod.ext
  · simp only [productAt_fst]
    exact congrFun ((prod.fst : X ⨯ Y ⟶ X).naturality j) z
  · simp only [productAt_snd]
    exact congrFun ((prod.snd : X ⨯ Y ⟶ Y).naturality j) z

variable {E F : SemiSimplexCategoryᵒᵖ ⥤ Type} {X Y : SSet.{0}}
variable (α : E ⟶ restrict X) (β : F ⟶ restrict Y)

/-- Evaluating both independent choices retains the original product normalization simplex. -/
def pairedForget : pairedChoices E F ⟶ restrict (X ⨯ Y) where
  app n e := (productAt X Y (inc.op.obj n)).symm (α.app n e.1, β.app n e.2)
  naturality {m n} j := by
    funext e
    apply (productAt X Y (inc.op.obj n)).injective
    change productAt X Y (inc.op.obj n)
        ((productAt X Y (inc.op.obj n)).symm
          (α.app n (E.map j e.1), β.app n (F.map j e.2))) =
      productAt X Y (inc.op.obj n)
        ((X ⨯ Y).map (inc.op.map j)
          ((productAt X Y (inc.op.obj m)).symm (α.app m e.1, β.app m e.2)))
    rw [productAt_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact Prod.ext (congrFun (α.naturality j) e.1) (congrFun (β.naturality j) e.2)

/-- Independent boundary lifts give a simultaneous lift over the exact ordered product. -/
theorem hasBoundaryLifting_paired (hα : HasBoundaryLifting α) (hβ : HasBoundaryLifting β) :
    HasBoundaryLifting (pairedForget α β) := by
  intro n y B hB
  let bL : Boundary E n :=
    { face := fun j h ↦ (B.face j h).1
      naturality := fun a j h ↦ congrArg _root_.Prod.fst (B.naturality a j h) }
  let bR : Boundary F n :=
    { face := fun j h ↦ (B.face j h).2
      naturality := fun a j h ↦ congrArg _root_.Prod.snd (B.naturality a j h) }
  have hL : bL.Over α (productAt X Y (op (inc.obj n)) y).1 := by
    intro m j h
    have he := congrArg (productAt X Y (op (inc.obj m))) (hB j h)
    change productAt X Y (op (inc.obj m))
        ((productAt X Y (op (inc.obj m))).symm
          (α.app (op m) (bL.face j h), β.app (op m) (bR.face j h))) = _ at he
    rw [Equiv.apply_symm_apply, productAt_map] at he
    exact congrArg _root_.Prod.fst he
  have hR : bR.Over β (productAt X Y (op (inc.obj n)) y).2 := by
    intro m j h
    have he := congrArg (productAt X Y (op (inc.obj m))) (hB j h)
    change productAt X Y (op (inc.obj m))
        ((productAt X Y (op (inc.obj m))).symm
          (α.app (op m) (bL.face j h), β.app (op m) (bR.face j h))) = _ at he
    rw [Equiv.apply_symm_apply, productAt_map] at he
    exact congrArg _root_.Prod.snd he
  obtain ⟨eL, heL, hfacesL⟩ := hα n _ bL hL
  obtain ⟨eR, heR, hfacesR⟩ := hβ n _ bR hR
  refine ⟨(eL, eR), ?_, ?_⟩
  · apply (productAt X Y (op (inc.obj n))).injective
    change productAt X Y (op (inc.obj n))
        ((productAt X Y (op (inc.obj n))).symm (α.app (op n) eL, β.app (op n) eR)) = _
    rw [Equiv.apply_symm_apply]
    exact Prod.ext heL heR
  · intro m j h
    exact Prod.ext (hfacesL j h) (hfacesR j h)

private abbrev Semi := SemiSimplexCategoryᵒᵖ ⥤ Type

/-- Pair presheaves and their actual maps by the pointwise binary product type. -/
def pairedChoiceFunctor : Semi × Semi ⥤ Semi :=
  prodFunctorToFunctorProd _ _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (Functor.uncurry.obj Types.binaryProductFunctor)

/-- Pair the pointwise product of simplicial sets as a bifunctor. -/
def simplicialProduct : SSet.{0} × SSet.{0} ⥤ SSet.{0} :=
  Functor.uncurry.obj prod.functor

theorem simplicialProduct_map {P Q : SSet.{0} × SSet.{0}} (f : P ⟶ Q) :
    simplicialProduct.map f = prod.map f.1 f.2 := by
  change prod.map f.1 (𝟙 _) ≫ prod.map (𝟙 _) f.2 = _
  rw [prod.map_map, Category.comp_id, Category.id_comp]

private theorem productAt_prodMap {U V : SSet.{0}} (f : X ⟶ U) (g : Y ⟶ V)
    (n : SimplexCategoryᵒᵖ) (z : (X ⨯ Y).obj n) :
    productAt U V n ((prod.map f g).app n z) =
      (f.app n (productAt X Y n z).1, g.app n (productAt X Y n z).2) := by
  apply Prod.ext
  · simp only [productAt_fst]
    exact congrFun (NatTrans.congr_app (prod.map_fst f g) n) z
  · simp only [productAt_snd]
    exact congrFun (NatTrans.congr_app (prod.map_snd f g) n) z

/-- Pairing the forgetful maps is natural for compatible maps of both
source presheaves and both original simplicial target spaces. -/
theorem pairedForget_natural {E' F' : Semi} {U V : SSet.{0}}
    {α' : E' ⟶ restrict U} {β' : F' ⟶ restrict V}
    (a : E ⟶ E') (b : F ⟶ F') (f : X ⟶ U) (g : Y ⟶ V)
    (ha : a ≫ α' = α ≫ Functor.whiskerLeft inc.op f)
    (hb : b ≫ β' = β ≫ Functor.whiskerLeft inc.op g) :
    pairedChoiceFunctor.map (a ×ₘ b) ≫ pairedForget α' β' =
      pairedForget α β ≫ Functor.whiskerLeft inc.op (prod.map f g) := by
  ext n z
  apply (productAt U V (inc.op.obj n)).injective
  change productAt U V (inc.op.obj n)
      ((productAt U V (inc.op.obj n)).symm
        (α'.app n (a.app n z.1), β'.app n (b.app n z.2))) =
    productAt U V (inc.op.obj n)
      ((prod.map f g).app _
        ((productAt X Y (inc.op.obj n)).symm (α.app n z.1, β.app n z.2)))
  rw [productAt_prodMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Prod.ext (congrFun (NatTrans.congr_app ha n) z.1)
    (congrFun (NatTrans.congr_app hb n) z.2)

end
end DaggerModels.PartII.SemiSimplexBoundaryLifting
