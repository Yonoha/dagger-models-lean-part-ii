import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv
import DaggerModelsPartII.JTJointEndpointLiftSpaceRestriction

/-! Map a complete fixed-square lift space while both source and target vary. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits MonoidalClosed Simplicial Opposite DaggerModels
open MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTVariableFixedLiftSpaceMap

noncomputable section

variable {A B X Y A' B' X' Y' : SSet.{0}}
variable {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
variable {t' : A' ⟶ X'} {i' : A' ⟶ B'} {p' : X' ⟶ Y'} {b' : B' ⟶ Y'}
variable (sq : CommSq t i p b) (sq' : CommSq t' i' p' b')
private def ambient (jB : B' ⟶ B) (qX : X ⟶ X') :
    (ihom B).obj X ⟶ (ihom B').obj X' :=
  (MonoidalClosed.pre jB).app X ≫ (ihom B').map qX

/-- A map of complete fixed-square lift spaces with changing source, target,
stationary value, and base. -/
def mapSquare (jA : A' ⟶ A) (jB : B' ⟶ B)
    (qX : X ⟶ X') (qY : Y ⟶ Y')
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t ≫ qX = t')
    (hp : p ≫ qY = qX ≫ p') (hb : jB ≫ b ≫ qY = b') :
    (SSet.ihomToPullbackFiber sq : SSet.{0}) ⟶
    SSet.ihomToPullbackFiber sq' :=
  SSet.Subcomplex.lift ((SSet.ihomToPullbackFiber sq).ι ≫ ambient jB qX) (by
    apply (SSet.range_le_ihomToPullbackFiber_iff sq' _).mpr
    constructor
    · simp only [ambient]
      rw [Category.assoc, Category.assoc]
      rw [← MonoidalClosed.pre_comm_ihom_map i' qX]
      rw [← Category.assoc ((MonoidalClosed.pre jB).app X)
        ((MonoidalClosed.pre i').app X) ((ihom A').map qX)]
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, ← hi,
        MonoidalClosed.pre_map, NatTrans.comp_app]
      simp only [← Category.assoc]
      rw [SSet.ihomToPullbackFiber_pre_app]
      rw [SSet.const_comp, ← SSet.ihom₀Equiv_symm_comp jA t,
        SSet.const_comp, ← SSet.ihom₀Equiv_symm_comp' (jA ≫ t) qX,
        Category.assoc, ht]
    · simp only [ambient]
      rw [Category.assoc, Category.assoc]
      rw [← Functor.map_comp, ← hp]
      rw [Functor.map_comp]
      rw [← Category.assoc ((MonoidalClosed.pre jB).app X)
        ((ihom B').map p) ((ihom B').map qY)]
      rw [MonoidalClosed.pre_comm_ihom_map jB p]
      simp only [← Category.assoc]
      rw [SSet.ihomToPullbackFiber_ihom_map]
      rw [SSet.const_comp, ← SSet.ihom₀Equiv_symm_comp jB b,
        SSet.const_comp, ← SSet.ihom₀Equiv_symm_comp' (jB ≫ b) qY,
        Category.assoc, hb])

@[reassoc]
theorem mapSquare_ι (jA : A' ⟶ A) (jB : B' ⟶ B)
    (qX : X ⟶ X') (qY : Y ⟶ Y')
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t ≫ qX = t')
    (hp : p ≫ qY = qX ≫ p') (hb : jB ≫ b ≫ qY = b') :
    mapSquare sq sq' jA jB qX qY hi ht hp hb ≫
    (SSet.ihomToPullbackFiber sq').ι =
      (SSet.ihomToPullbackFiber sq).ι ≫ ambient jB qX := rfl

/-- On a simplex, the changing-square map is precomposition in the domain
and postcomposition in the value. -/
theorem timeMap_mapSquare (jA : A' ⟶ A) (jB : B' ⟶ B)
    (qX : X ⟶ X') (qY : Y ⟶ Y')
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t ≫ qX = t')
    (hp : p ≫ qY = qX ≫ p') (hb : jB ≫ b ≫ qY = b')
    (n : SimplexCategory)
    (x : (SSet.ihomToPullbackFiber sq).obj (op n)) :
    JTFixedLiftSpaceTimeEquiv.timeMap sq' n
        ((mapSquare sq sq' jA jB qX qY hi ht hp hb).app _ x) =
      (jB ▷ SSet.stdSimplex.obj n) ≫
        JTFixedLiftSpaceTimeEquiv.timeMap sq n x ≫ qX := by
  have h : SSet.yonedaEquiv.symm
      ((mapSquare sq sq' jA jB qX qY hi ht hp hb).app _ x) ≫
        (SSet.ihomToPullbackFiber sq').ι =
      (SSet.yonedaEquiv.symm x ≫ (SSet.ihomToPullbackFiber sq).ι) ≫
        ambient jB qX := by
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
      mapSquare_ι, Category.assoc]
  unfold JTFixedLiftSpaceTimeEquiv.timeMap
  rw [h]
  simp only [ambient, ← Category.assoc]
  rw [uncurry_natural_right, uncurry_pre_app]

/-- At degree zero the map acts by ordinary precomposition and
postcomposition. -/
theorem mapSquare_zero (jA : A' ⟶ A) (jB : B' ⟶ B)
    (qX : X ⟶ X') (qY : Y ⟶ Y')
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t ≫ qX = t')
    (hp : p ≫ qY = qX ≫ p') (hb : jB ≫ b ≫ qY = b')
    (v : (SSet.ihomToPullbackFiber sq).obj (op ⦋0⦌)) :
    SSet.ihom₀Equiv
        (((mapSquare sq sq' jA jB qX qY hi ht hp hb).app _ v).val) =
      jB ≫ SSet.ihom₀Equiv v.val ≫ qX := by
  apply SSet.ihom₀Equiv.symm.injective
  rw [Equiv.symm_apply_apply,
    SSet.ihom₀Equiv_symm_comp jB
      (SSet.ihom₀Equiv v.val ≫ qX),
    SSet.ihom₀Equiv_symm_comp'
      (SSet.ihom₀Equiv v.val) qX,
    Equiv.symm_apply_apply]
  exact congrFun
    (NatTrans.congr_app
      (mapSquare_ι sq sq' jA jB qX qY hi ht hp hb) (op ⦋0⦌)) v

end
end DaggerModels.PartII.JTVariableFixedLiftSpaceMap
