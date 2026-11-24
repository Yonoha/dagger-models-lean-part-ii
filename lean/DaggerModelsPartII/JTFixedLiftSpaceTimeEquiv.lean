import DaggerModelsPartII.JTFixedLiftSpacePrecomp
import DaggerModelsPartII.ParameterVertexLiftSpace

/-!
# Simplices of an exact fixed-square lift space as time-dependent maps
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFixedLiftSpaceTimeEquiv

noncomputable section

variable {A B X Y : SSet.{u}} {t : A ⟶ X} {i : A ⟶ B}
variable {p : X ⟶ Y} {b : B ⟶ Y}

/-- Full maps on a coefficient object and a time simplex, with the exact
stationary and over-base equations. -/
def TimeLift (_sq : CommSq t i p b) (n : SimplexCategory) : Type u :=
  {v : B ⊗ SSet.stdSimplex.obj n ⟶ X //
    (i ▷ SSet.stdSimplex.obj n) ≫ v = fst A (SSet.stdSimplex.obj n) ≫ t ∧
    v ≫ p = fst B (SSet.stdSimplex.obj n) ≫ b}

private theorem range_curry_iff (sq : CommSq t i p b) (T : SSet.{u})
    (v : B ⊗ T ⟶ X) :
    SSet.Subcomplex.range (curry v) ≤ SSet.ihomToPullbackFiber sq ↔
      (i ▷ T) ≫ v = fst A T ≫ t ∧
      v ≫ p = fst B T ≫ b := by
  rw [SSet.range_le_ihomToPullbackFiber_iff sq]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · simpa only [uncurry_pre_app, uncurry_curry,
        SSet.const_ihom₀Equiv_symm_apply] using congrArg uncurry h₁
    · simpa only [uncurry_natural_right, uncurry_curry,
        SSet.const_ihom₀Equiv_symm_apply] using congrArg uncurry h₂
  · rintro ⟨h₁, h₂⟩
    constructor
    · rw [curry_pre_app, SSet.const_ihom₀Equiv_symm_apply, h₁]
    · rw [← curry_natural_right, SSet.const_ihom₀Equiv_symm_apply, h₂]

/-- Extend a prescribed time-dependent map from any simplicial time
subobject, with both original fixed-square equations. -/
theorem exists_extend_time (sq : CommSq t i p b) [Mono i] [WeakEquivalence i] [Fibration p]
    {C T : SSet.{u}} (j : C ⟶ T) [Mono j] (v : B ⊗ C ⟶ X)
    (hstat : (i ▷ C) ≫ v = fst A C ≫ t)
    (hbase : v ≫ p = fst B C ≫ b) :
    ∃ w : B ⊗ T ⟶ X, (B ◁ j) ≫ w = v ∧
      (i ▷ T) ≫ w = fst A T ≫ t ∧ w ≫ p = fst B T ≫ b := by
  let F := SSet.ihomToPullbackFiber sq
  let g := SSet.Subcomplex.lift (curry v) ((range_curry_iff sq C v).2 ⟨hstat, hbase⟩)
  let P := SSet.stdSimplex.isTerminalObj₀.from (F : SSet.{u})
  haveI : IsFibrant (F : SSet.{u}) := ParameterVertexLiftSpace.fixedSquare_liftSpace_kan sq
  haveI : Fibration P :=
    (isFibrant_iff_of_isTerminal P SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  haveI : WeakEquivalence P := ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak sq
  haveI : Cofibration j := SSet.modelCategoryQuillen.cofibration_of_mono _
  let S : CommSq g j P (SSet.stdSimplex.isTerminalObj₀.from T) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  let w := uncurry (S.lift ≫ F.ι)
  have hrange : SSet.Subcomplex.range (curry w) ≤ F := by
    rw [curry_uncurry]
    exact (Subfunctor.range_comp_le _ _).trans_eq (SSet.Subcomplex.range_ι F)
  have h := (range_curry_iff sq T w).1 hrange
  refine ⟨w, ?_, h.1, h.2⟩
  change (B ◁ j) ≫ uncurry (S.lift ≫ F.ι) = v
  rw [← uncurry_natural_left, ← Category.assoc, S.fac_left]
  rw [SSet.Subcomplex.lift_ι, uncurry_curry]

/-- The full map represented by a simplex of the exact lift space. -/
def timeMap (sq : CommSq t i p b) (n : SimplexCategory)
    (x : (SSet.ihomToPullbackFiber sq).obj (Opposite.op n)) :
    B ⊗ SSet.stdSimplex.obj n ⟶ X :=
  uncurry (SSet.yonedaEquiv.symm x ≫ (SSet.ihomToPullbackFiber sq).ι)

theorem timeMap_eq (sq : CommSq t i p b) (n : SimplexCategory)
    (x : (SSet.ihomToPullbackFiber sq).obj (Opposite.op n)) :
    curry (timeMap sq n x) =
      SSet.yonedaEquiv.symm x ≫ (SSet.ihomToPullbackFiber sq).ι := by
  simp [timeMap]

theorem timeMap_conditions (sq : CommSq t i p b) (n : SimplexCategory)
    (x : (SSet.ihomToPullbackFiber sq).obj (Opposite.op n)) :
    (i ▷ SSet.stdSimplex.obj n) ≫ timeMap sq n x =
        fst A (SSet.stdSimplex.obj n) ≫ t ∧
      timeMap sq n x ≫ p = fst B (SSet.stdSimplex.obj n) ≫ b := by
  apply (range_curry_iff sq (SSet.stdSimplex.obj n) (timeMap sq n x)).mp
  rw [timeMap_eq]
  calc
    SSet.Subcomplex.range
        (SSet.yonedaEquiv.symm x ≫ (SSet.ihomToPullbackFiber sq).ι) ≤
        SSet.Subcomplex.range (SSet.ihomToPullbackFiber sq).ι :=
      Subfunctor.range_comp_le _ _
    _ = SSet.ihomToPullbackFiber sq := SSet.Subcomplex.range_ι _

/-- The all-dimensional identification of simplices with exact time-dependent
lift maps. -/
def timeEquiv (sq : CommSq t i p b) (n : SimplexCategory) :
    (SSet.ihomToPullbackFiber sq).obj (Opposite.op n) ≃ TimeLift sq n where
  toFun x := ⟨timeMap sq n x, timeMap_conditions sq n x⟩
  invFun v := SSet.yonedaEquiv
    (SSet.Subcomplex.lift (curry v.1) ((range_curry_iff sq (SSet.stdSimplex.obj n) v.1).mpr v.2))
  left_inv x := by
    apply SSet.yonedaEquiv.symm.injective
    apply (cancel_mono (SSet.ihomToPullbackFiber sq).ι).mp
    simp [timeMap]
  right_inv v := by
    apply Subtype.ext
    change uncurry (SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv (SSet.Subcomplex.lift (curry v.1)
        ((range_curry_iff sq (SSet.stdSimplex.obj n) v.1).mpr v.2))) ≫
        (SSet.ihomToPullbackFiber sq).ι) = v.1
    simp

theorem timeEquiv_apply_val (sq : CommSq t i p b) (n : SimplexCategory)
    (x : (SSet.ihomToPullbackFiber sq).obj (Opposite.op n)) :
    (timeEquiv sq n x).1 = timeMap sq n x := rfl

/-- Restricting the time simplex restricts the full map in its time variable. -/
theorem timeMap_map (sq : CommSq t i p b) {m n : SimplexCategory}
    (α : m ⟶ n) (x : (SSet.ihomToPullbackFiber sq).obj (Opposite.op n)) :
    timeMap sq m ((SSet.ihomToPullbackFiber sq : SSet.{u}).map α.op x) =
      (B ◁ SSet.stdSimplex.map α) ≫ timeMap sq n x := by
  unfold timeMap
  rw [SSet.yonedaEquiv_symm_map, Category.assoc, uncurry_natural_left]

/-- Restriction in the coefficient variable is precomposition on full maps. -/
theorem timeMap_precomp {C : SSet.{u}} {iC : A ⟶ C} {bC : C ⟶ Y}
    (sqB : CommSq t i p b) (sqC : CommSq t iC p bC)
    (j : B ⟶ C) (hi : i ≫ j = iC) (hb : j ≫ bC = b)
    (n : SimplexCategory)
    (x : (SSet.ihomToPullbackFiber sqC).obj (Opposite.op n)) :
    timeMap sqB n ((JTFixedLiftSpacePrecomp.precomp sqB sqC j hi hb).app _ x) =
      (j ▷ SSet.stdSimplex.obj n) ≫ timeMap sqC n x := by
  have h : SSet.yonedaEquiv.symm
      ((JTFixedLiftSpacePrecomp.precomp sqB sqC j hi hb).app _ x) ≫
        (SSet.ihomToPullbackFiber sqB).ι =
      (SSet.yonedaEquiv.symm x ≫ (SSet.ihomToPullbackFiber sqC).ι) ≫
        (MonoidalClosed.pre j).app X := by
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
      JTFixedLiftSpacePrecomp.precomp_ι, Category.assoc]
  unfold timeMap
  rw [h, uncurry_pre_app]

end

end DaggerModels.PartII.JTFixedLiftSpaceTimeEquiv
