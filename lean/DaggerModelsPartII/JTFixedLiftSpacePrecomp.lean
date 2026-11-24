import DaggerModelsPartII.ParameterVertexLiftSpace

/-!
# Restriction of exact fixed-square lift spaces
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalClosed Simplicial
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFixedLiftSpacePrecomp

noncomputable section

variable {A B C D X Y : SSet.{u}} {t : A ⟶ X} {p : X ⟶ Y}
variable {iB : A ⟶ B} {iC : A ⟶ C} {iD : A ⟶ D}
variable {bB : B ⟶ Y} {bC : C ⟶ Y} {bD : D ⟶ Y}

/-- Restrict a complete coefficient family along a map over the exact base
and under the prescribed stationary value. -/
def precomp (sqB : CommSq t iB p bB) (sqC : CommSq t iC p bC)
    (j : B ⟶ C) (hi : iB ≫ j = iC) (hb : j ≫ bC = bB) :
    (SSet.ihomToPullbackFiber sqC : SSet.{u}) ⟶ SSet.ihomToPullbackFiber sqB :=
  SSet.Subcomplex.lift ((SSet.ihomToPullbackFiber sqC).ι ≫ (MonoidalClosed.pre j).app X) (by
    apply (SSet.range_le_ihomToPullbackFiber_iff sqB _).mpr
    constructor
    · rw [Category.assoc, ← NatTrans.comp_app, ← MonoidalClosed.pre_map, hi,
        SSet.ihomToPullbackFiber_pre_app]
    · rw [Category.assoc, MonoidalClosed.pre_comm_ihom_map, ← Category.assoc,
        SSet.ihomToPullbackFiber_ihom_map, SSet.const_comp, ← SSet.ihom₀Equiv_symm_comp, hb])

@[reassoc]
theorem precomp_ι (sqB : CommSq t iB p bB) (sqC : CommSq t iC p bC)
    (j : B ⟶ C) (hi : iB ≫ j = iC) (hb : j ≫ bC = bB) :
    precomp sqB sqC j hi hb ≫ (SSet.ihomToPullbackFiber sqB).ι =
      (SSet.ihomToPullbackFiber sqC).ι ≫ (MonoidalClosed.pre j).app X := rfl

theorem precomp_id (sqB : CommSq t iB p bB)
    (hi : iB ≫ 𝟙 B = iB) (hb : 𝟙 B ≫ bB = bB) :
    precomp sqB sqB (𝟙 B) hi hb = 𝟙 _ := by
  apply (cancel_mono (SSet.ihomToPullbackFiber sqB).ι).mp
  rw [precomp_ι, MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

theorem precomp_comp (sqB : CommSq t iB p bB) (sqC : CommSq t iC p bC)
    (sqD : CommSq t iD p bD)
    (j : B ⟶ C) (k : C ⟶ D)
    (hij : iB ≫ j = iC) (hbj : j ≫ bC = bB)
    (hik : iC ≫ k = iD) (hbk : k ≫ bD = bC)
    (hi : iB ≫ (j ≫ k) = iD) (hb : (j ≫ k) ≫ bD = bB) :
    precomp sqC sqD k hik hbk ≫ precomp sqB sqC j hij hbj =
      precomp sqB sqD (j ≫ k) hi hb := by
  apply (cancel_mono (SSet.ihomToPullbackFiber sqB).ι).mp
  rw [Category.assoc, precomp_ι, precomp_ι_assoc, precomp_ι, MonoidalClosed.pre_map, NatTrans.comp_app]

theorem precomp_id_of_eq (sqB : CommSq t iB p bB) (j : B ⟶ B) (hj : j = 𝟙 B)
    (hi : iB ≫ j = iB) (hb : j ≫ bB = bB) :
    precomp sqB sqB j hi hb = 𝟙 _ := by
  subst j
  exact precomp_id sqB hi hb

theorem precomp_comp_of_fac (sqB : CommSq t iB p bB) (sqC : CommSq t iC p bC)
    (sqD : CommSq t iD p bD)
    (j : B ⟶ C) (k : C ⟶ D) (l : B ⟶ D) (fac : j ≫ k = l)
    (hij : iB ≫ j = iC) (hbj : j ≫ bC = bB)
    (hik : iC ≫ k = iD) (hbk : k ≫ bD = bC)
    (hil : iB ≫ l = iD) (hbl : l ≫ bD = bB) :
    precomp sqC sqD k hik hbk ≫ precomp sqB sqC j hij hbj =
      precomp sqB sqD l hil hbl := by
  subst l
  exact precomp_comp sqB sqC sqD j k hij hbj hik hbk hil hbl

/-- On vertices this is precomposition of the two original lift maps. -/
theorem precomp_zero (sqB : CommSq t iB p bB) (sqC : CommSq t iC p bC)
    (j : B ⟶ C) (hi : iB ≫ j = iC) (hb : j ≫ bC = bB)
    (v : (SSet.ihomToPullbackFiber sqC).obj (Opposite.op ⦋0⦌)) :
    SSet.ihom₀Equiv (((precomp sqB sqC j hi hb).app _ v).val) =
      j ≫ SSet.ihom₀Equiv v.val := by
  apply SSet.ihom₀Equiv.symm.injective
  rw [Equiv.symm_apply_apply, SSet.ihom₀Equiv_symm_comp, Equiv.symm_apply_apply]
  exact congrFun (NatTrans.congr_app (precomp_ι sqB sqC j hi hb) (Opposite.op ⦋0⦌)) v

/-- Between Kan weak inclusions the restriction is itself a Kan weak
equivalence of the actual lift spaces. -/
theorem precomp_weak (sqB : CommSq t iB p bB) (sqC : CommSq t iC p bC)
    [Mono iB] [WeakEquivalence iB] [Mono iC] [WeakEquivalence iC] [Fibration p]
    (j : B ⟶ C) (hi : iB ≫ j = iC) (hb : j ≫ bC = bB) :
    WeakEquivalence (precomp sqB sqC j hi hb) := by
  haveI := ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak sqB
  haveI := ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak sqC
  have h : precomp sqB sqC j hi hb ≫
      SSet.stdSimplex.isTerminalObj₀.from (SSet.ihomToPullbackFiber sqB : SSet.{u}) =
        SSet.stdSimplex.isTerminalObj₀.from (SSet.ihomToPullbackFiber sqC : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact weakEquivalence_of_postcomp_of_fac h

end

end DaggerModels.PartII.JTFixedLiftSpacePrecomp
