import BisimplicialBaseSimplexFibers
import Mathlib.CategoryTheory.Elements
import NerveHomotopy

/-!
# The fixed vertical column of the comma fiber diagram

The forgetful functor retains the original total-row simplex and its
outer index. Its candidate section uses the represented simplex of
that same point, in the unchanged standard-simplex comma category.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerModels.PartII.BisimplicialBaseSimplexFibers
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialCommaColumnRetraction

noncomputable section

variable (f : Arrow BiSSet.{0}) (k : SimplexCategoryᵒᵖ)

private abbrev L : Index f ⥤ Type :=
  fiberDiagram f ⋙ SSet.evaluation.obj k

private abbrev K : SimplexCategoryᵒᵖ ⥤ Type :=
  f.left ⋙ SSet.evaluation.obj k

/-- Forget the specified base simplex and retain the actual total-row
coordinate. Both the outer arrow and original point remain literal. -/
def forget : (L f k).Elements ⥤ (K f k).Elements where
  obj P := ⟨P.1.right,
    (pullback.fst (f.hom.app P.1.right) P.1.hom).app k P.2⟩
  map {P Q} a := ⟨a.val.right, by
    have h := congrFun
      (NatTrans.congr_app (fiberMap_fst f a.val) k) P.2
    change (fiberMap f a.val ≫
        pullback.fst (f.hom.app Q.1.right) Q.1.hom).app k P.2 =
      (pullback.fst (f.hom.app P.1.right) P.1.hom ≫
        f.left.map a.val.right).app k P.2 at h
    change (pullback.fst (f.hom.app Q.1.right) Q.1.hom).app k
        ((fiberMap f a.val).app k P.2) =
      (f.left.map a.val.right).app k
        ((pullback.fst (f.hom.app P.1.right) P.1.hom).app k P.2) at h
    have ha : (fiberMap f a.val).app k P.2 = Q.2 := a.property
    rw [ha] at h
    exact h.symm⟩
  map_id _ := by apply CategoryOfElements.ext; rfl
  map_comp _ _ := by apply CategoryOfElements.ext; rfl

/-- Represent the same actual total-row simplex as a comma object,
with left standard-simplex degree exactly `k.unop`. -/
def sectionIndex (P : (K f k).Elements) : Index f :=
  ⟨k.unop, P.1,
    (SSet.yonedaEquiv (X := f.right.obj P.1) (n := k.unop)).symm
      ((f.hom.app P.1).app k P.2)⟩

private def identitySimplex : (SSet.stdSimplex.obj k.unop).obj k :=
  SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj k.unop))

private theorem yoneda_at_identity (Y : SSet.{0}) (x : Y.obj k) :
    (SSet.yonedaEquiv.symm x).app k (identitySimplex k) = x := by
  cases k with
  | op n =>
      induction n using SimplexCategory.rec with
      | _ n => exact SSet.yonedaEquiv_symm_app_id x

/-- The full strict-pullback point represented by the same original
simplex and the identity standard-simplex parameter. -/
def sectionPoint (P : (K f k).Elements) :
    (fiber f (sectionIndex f k P)).obj k :=
  (pullback.lift
    ((SSet.yonedaEquiv (X := f.left.obj P.1) (n := k.unop)).symm P.2)
    (𝟙 (SSet.stdSimplex.obj k.unop))
    (by
      rw [SSet.yonedaEquiv_symm_comp]
      rfl)).app k (identitySimplex k)

/-- The section point remembers precisely its original total-row
coordinate. -/
theorem sectionPoint_fst (P : (K f k).Elements) :
    (pullback.fst (f.hom.app P.1) (sectionIndex f k P).hom).app k
      (sectionPoint f k P) = P.2 := by
  have h := congrFun (NatTrans.congr_app
    (pullback.lift_fst (f := f.hom.app P.1) (g := (sectionIndex f k P).hom)
      ((SSet.yonedaEquiv (X := f.left.obj P.1) (n := k.unop)).symm P.2)
      (𝟙 (SSet.stdSimplex.obj k.unop))
      ((SSet.yonedaEquiv_symm_comp (X := f.left.obj P.1)
        (Y := f.right.obj P.1) (n := k.unop) P.2 (f.hom.app P.1)).trans
        (Category.id_comp _).symm)) k)
      (identitySimplex k)
  change _ = ((SSet.yonedaEquiv
    (X := f.left.obj P.1) (n := k.unop)).symm P.2).app k (identitySimplex k) at h
  exact h.trans (yoneda_at_identity k (f.left.obj P.1) P.2)

/-- The represented section object in the original fiber diagram. -/
def sectionObject (P : (K f k).Elements) : (L f k).Elements :=
  ⟨sectionIndex f k P, sectionPoint f k P⟩

/-- The objectwise section-forget roundtrip is literally the identity
on the outer index and original total-row point. -/
theorem sectionObject_forget (P : (K f k).Elements) :
    (forget f k).obj (sectionObject f k P) = P := by
  refine Functor.Elements.ext _ _ rfl ?_
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply]
  exact sectionPoint_fst f k P

/-- The section point has the identity parameter in the standard
simplex on its chosen degree. -/
theorem sectionPoint_snd (P : (K f k).Elements) :
    (pullback.snd (f.hom.app P.1) (sectionIndex f k P).hom).app k
      (sectionPoint f k P) = identitySimplex k := by
  have h := congrFun (NatTrans.congr_app
    (pullback.lift_snd (f := f.hom.app P.1) (g := (sectionIndex f k P).hom)
      ((SSet.yonedaEquiv (X := f.left.obj P.1) (n := k.unop)).symm P.2)
      (𝟙 (SSet.stdSimplex.obj k.unop))
      ((SSet.yonedaEquiv_symm_comp (X := f.left.obj P.1)
        (Y := f.right.obj P.1) (n := k.unop) P.2 (f.hom.app P.1)).trans
        (Category.id_comp _).symm)) k)
      (identitySimplex k)
  exact h

/-- An original outer operator gives the section's comma operator;
the standard-simplex degree remains exactly fixed at `k`. -/
def sectionIndexMap {P Q : (K f k).Elements} (a : P ⟶ Q) :
    sectionIndex f k P ⟶ sectionIndex f k Q where
  left := 𝟙 k.unop
  right := a.val
  w := by
    have h := congrFun (NatTrans.congr_app (f.hom.naturality a.val) k) P.2
    change (f.hom.app Q.1).app k ((f.left.map a.val).app k P.2) =
      (f.right.map a.val).app k ((f.hom.app P.1).app k P.2) at h
    have ha : (f.left.map a.val).app k P.2 = Q.2 := a.property
    rw [ha] at h
    have hs : (sectionIndex f k P).hom ≫ f.right.map a.val =
        (sectionIndex f k Q).hom := by
      dsimp only [sectionIndex]
      rw [SSet.yonedaEquiv_symm_comp, ← h]
    exact ((congrArg (fun m ↦ m ≫ (sectionIndex f k Q).hom)
      (SSet.stdSimplex.map_id k.unop)).trans (Category.id_comp _)).trans hs.symm

/-- The section's comma arrow carries its represented pullback point
to the represented point at the target outer index. -/
theorem sectionPoint_map {P Q : (K f k).Elements} (a : P ⟶ Q) :
    (fiberMap f (sectionIndexMap f k a)).app k (sectionPoint f k P) =
      sectionPoint f k Q := by
  apply (FunctorToTypes.pullback_ext).mpr
  constructor
  · have h := congrFun
      (NatTrans.congr_app (fiberMap_fst f (sectionIndexMap f k a)) k)
      (sectionPoint f k P)
    change (pullback.fst (f.hom.app Q.1) (sectionIndex f k Q).hom).app k
        ((fiberMap f (sectionIndexMap f k a)).app k (sectionPoint f k P)) =
      (f.left.map a.val).app k
        ((pullback.fst (f.hom.app P.1) (sectionIndex f k P).hom).app k
          (sectionPoint f k P)) at h
    rw [sectionPoint_fst] at h
    have ha : (f.left.map a.val).app k P.2 = Q.2 := a.property
    rw [ha] at h
    exact h.trans (sectionPoint_fst f k Q).symm
  · have h := congrFun
      (NatTrans.congr_app (fiberMap_snd f (sectionIndexMap f k a)) k)
      (sectionPoint f k P)
    change (pullback.snd (f.hom.app Q.1) (sectionIndex f k Q).hom).app k
        ((fiberMap f (sectionIndexMap f k a)).app k (sectionPoint f k P)) =
      (SSet.stdSimplex.map (𝟙 k.unop)).app k
        ((pullback.snd (f.hom.app P.1) (sectionIndex f k P).hom).app k
          (sectionPoint f k P)) at h
    rw [sectionPoint_snd] at h
    have hm := congrFun (NatTrans.congr_app
      (SSet.stdSimplex.map_id k.unop) k) (identitySimplex k)
    exact (h.trans hm).trans (sectionPoint_snd f k Q).symm

/-- The represented section on complete Elements objects and arrows. -/
def sectionFunctor : (K f k).Elements ⥤ (L f k).Elements where
  obj := sectionObject f k
  map {P Q} a := ⟨sectionIndexMap f k a, sectionPoint_map f k a⟩
  map_id P := by
    apply CategoryOfElements.ext
    apply Comma.hom_ext <;> rfl
  map_comp a b := by
    apply CategoryOfElements.ext
    apply Comma.hom_ext <;> rfl

private theorem eqToHom_val {D : Type} [SmallCategory D] {T : D ⥤ Type}
    {P Q : T.Elements} (h : P = Q) :
    (eqToHom h : P ⟶ Q).val = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

/-- The represented section is a strict right inverse of the forget
functor on both objects and arrows. -/
theorem section_forget : sectionFunctor f k ⋙ forget f k = 𝟭 (K f k).Elements := by
  refine CategoryTheory.Functor.ext (sectionObject_forget f k) ?_
  intro P Q a
  apply CategoryOfElements.ext
  simp only [CategoryOfElements.comp_val, eqToHom_val, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  rfl

#print axioms forget
#print axioms sectionPoint_fst
#print axioms sectionObject_forget
#print axioms sectionPoint_snd
#print axioms sectionIndexMap
#print axioms sectionPoint_map
#print axioms section_forget

end
end DaggerModels.PartII.BisimplicialCommaColumnRetraction
