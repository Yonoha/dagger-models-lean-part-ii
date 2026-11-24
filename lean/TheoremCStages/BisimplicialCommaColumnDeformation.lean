import BisimplicialCommaColumnRetraction
import TopCatModelCategory.SSet.StandardSimplex

/-!
# The comma-parameter deformation in one fixed vertical column

The deformation uses the actual parameter simplex of each original
pullback point. Its outer coordinate is the identity, while its
standard-simplex coordinate is the represented original parameter.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerModels.PartII.BisimplicialBaseSimplexFibers
open DaggerModels.PartII.BisimplicialCommaColumnRetraction
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialCommaColumnDeformation

noncomputable section

variable (f : Arrow BiSSet.{0}) (k : SimplexCategoryᵒᵖ)

private abbrev L : Index f ⥤ Type :=
  fiberDiagram f ⋙ SSet.evaluation.obj k

private abbrev K : SimplexCategoryᵒᵖ ⥤ Type :=
  f.left ⋙ SSet.evaluation.obj k

/-- The original standard-simplex parameter of a strict pullback
point, interpreted as a genuine simplex-category arrow. -/
def parameter (P : (L f k).Elements) : k.unop ⟶ P.1.left :=
  SSet.stdSimplex.objEquiv
    ((pullback.snd (f.hom.app P.1.right) P.1.hom).app k P.2)

/-- The comma arrow from the represented section back to the original
base-simplex parameter; its outer component is literally the identity. -/
def deformationIndexMap (P : (L f k).Elements) :
    sectionIndex f k ((forget f k).obj P) ⟶ P.1 where
  left := parameter f k P
  right := 𝟙 P.1.right
  w := by
    have hp := congrFun
      (NatTrans.congr_app
        (pullback.condition (f := f.hom.app P.1.right) (g := P.1.hom)) k) P.2
    change (f.hom.app P.1.right).app k
        ((pullback.fst (f.hom.app P.1.right) P.1.hom).app k P.2) =
      P.1.hom.app k
        ((pullback.snd (f.hom.app P.1.right) P.1.hom).app k P.2) at hp
    have ht := SSet.yonedaEquiv_symm_app_apply
      (SSet.yonedaEquiv P.1.hom)
      ((pullback.snd (f.hom.app P.1.right) P.1.hom).app k P.2)
    rw [SSet.yonedaEquiv.symm_apply_apply] at ht
    have hs : SSet.stdSimplex.map (parameter f k P) ≫ P.1.hom =
        (sectionIndex f k ((forget f k).obj P)).hom := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_map_comp]
      have hy := (SSet.yonedaEquiv
        (X := f.right.obj P.1.right) (n := k.unop)).apply_symm_apply
          ((f.hom.app P.1.right).app k
            ((pullback.fst (f.hom.app P.1.right) P.1.hom).app k P.2))
      exact ht.symm.trans (hp.symm.trans hy.symm)
    exact hs.trans ((congrArg
      (fun m ↦ (sectionIndex f k ((forget f k).obj P)).hom ≫ m)
      (f.right.map_id P.1.right)).trans (Category.comp_id _)).symm

/-- The original parameter is recovered when the section's identity
simplex is transported along the comma deformation arrow. -/
theorem parameter_identity (P : (L f k).Elements) :
    (SSet.stdSimplex.map (parameter f k P)).app k
      (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj k.unop))) =
      (pullback.snd (f.hom.app P.1.right) P.1.hom).app k P.2 := by
  change SSet.yonedaEquiv (SSet.stdSimplex.map (parameter f k P)) = _
  rw [SSet.stdSimplex.yonedaEquiv_map]
  exact SSet.stdSimplex.objEquiv.symm_apply_apply _

/-- Transporting the represented strict-pullback point along the
actual comma arrow recovers the entire original strict-pullback point. -/
theorem deformationPoint (P : (L f k).Elements) :
    (fiberMap f (deformationIndexMap f k P)).app k
        (sectionPoint f k ((forget f k).obj P)) = P.2 := by
  apply (FunctorToTypes.pullback_ext).mpr
  constructor
  · have h := congrFun
      (NatTrans.congr_app (fiberMap_fst f (deformationIndexMap f k P)) k)
      (sectionPoint f k ((forget f k).obj P))
    change (pullback.fst (f.hom.app P.1.right) P.1.hom).app k
        ((fiberMap f (deformationIndexMap f k P)).app k
          (sectionPoint f k ((forget f k).obj P))) =
      (f.left.map (𝟙 P.1.right)).app k
        ((pullback.fst (f.hom.app P.1.right)
          (sectionIndex f k ((forget f k).obj P)).hom).app k
          (sectionPoint f k ((forget f k).obj P))) at h
    exact h.trans ((congrArg ((f.left.map (𝟙 P.1.right)).app k)
      (sectionPoint_fst f k ((forget f k).obj P))).trans
        (congrFun (NatTrans.congr_app (f.left.map_id P.1.right) k)
          ((forget f k).obj P).2))
  · have h := congrFun
      (NatTrans.congr_app (fiberMap_snd f (deformationIndexMap f k P)) k)
      (sectionPoint f k ((forget f k).obj P))
    change (pullback.snd (f.hom.app P.1.right) P.1.hom).app k
        ((fiberMap f (deformationIndexMap f k P)).app k
          (sectionPoint f k ((forget f k).obj P))) =
      (SSet.stdSimplex.map (parameter f k P)).app k
        ((pullback.snd (f.hom.app P.1.right)
          (sectionIndex f k ((forget f k).obj P)).hom).app k
          (sectionPoint f k ((forget f k).obj P))) at h
    exact h.trans ((congrArg ((SSet.stdSimplex.map (parameter f k P)).app k)
      (sectionPoint_snd f k ((forget f k).obj P))).trans
        (parameter_identity f k P))

/-- The section-forget composite deforms to the identity on the full
Elements category, without dropping either comma coordinate. -/
def deformation : forget f k ⋙ sectionFunctor f k ⟶ 𝟭 (L f k).Elements where
  app P := ⟨deformationIndexMap f k P, deformationPoint f k P⟩
  naturality {P Q} a := by
    apply CategoryOfElements.ext
    apply Comma.hom_ext
    · have hs := congrFun (NatTrans.congr_app (fiberMap_snd f a.val) k) P.2
      change (pullback.snd (f.hom.app Q.1.right) Q.1.hom).app k
          ((fiberMap f a.val).app k P.2) =
        (SSet.stdSimplex.map a.val.left).app k
          ((pullback.snd (f.hom.app P.1.right) P.1.hom).app k P.2) at hs
      have ha : (fiberMap f a.val).app k P.2 = Q.2 := a.property
      rw [ha] at hs
      change 𝟙 k.unop ≫ parameter f k Q = parameter f k P ≫ a.val.left
      exact (Category.id_comp _).trans (congrArg SSet.stdSimplex.objEquiv hs)
    · rfl

/-- The column forget functor is nerve-weak by its explicit section
and actual comma-parameter deformation. -/
theorem nerve_forget_weak : WeakEquivalence (nerveMap (forget f k)) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW (forget f k) (sectionFunctor f k)
      (Relation.EqvGen.rel _ _ ⟨deformation f k⟩)
      (Relation.EqvGen.rel _ _ ⟨eqToHom (section_forget f k)⟩))

#print axioms deformationIndexMap
#print axioms deformationPoint
#print axioms deformation
#print axioms nerve_forget_weak

end
end DaggerModels.PartII.BisimplicialCommaColumnDeformation
