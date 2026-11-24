import DaggerModelsPartII.ChosenHomotopyFiberFunctor
import NativeFibrationWeakFromVertexFibres

/-! Weakness of an actual map on strict fibers is constant on each component of the base. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSSetFibrationSquareFibreWeak
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FibrationSquareComponentFibers

noncomputable section

variable {X Y B D : SSet.{0}} (p : X ⟶ B) (q : Y ⟶ D)
  (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)

private def overPoint {K L : SSet.{0}} (c : L ⟶ B) (b : K ⟶ L) :
    pullback p (b ≫ c) ⟶ pullback p c :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b) (by
    rw [Category.assoc, pullback.condition])

private theorem overPoint_weak {K L : SSet.{0}} (c : L ⟶ B) (b : K ⟶ L)
    [Fibration p] [WeakEquivalence b] : WeakEquivalence (overPoint p c b) := by
  have hs : IsPullback (overPoint p c b) (pullback.snd p (b ≫ c)) (pullback.snd p c) b :=
    IsPullback.of_right (by
      simpa only [overPoint, pullback.lift_fst] using IsPullback.of_hasPullback p (b ≫ c))
      (by simp [overPoint]) (IsPullback.of_hasPullback p c)
  exact DaggerSSetRightProper.weakEquivalence_of_isPullback hs

private theorem overPoint_natural {K L : SSet.{0}} (c : L ⟶ B) (b : K ⟶ L) :
    overPoint p c b ≫ fibreMap p q f g h c (c ≫ g) rfl =
      fibreMap p q f g h (b ≫ c) (b ≫ (c ≫ g)) (Category.assoc _ _ _) ≫
        overPoint q (c ≫ g) b := by
  apply pullback.hom_ext
  · simp [Category.assoc, overPoint, fibreMap_fst]
  · simp [Category.assoc, overPoint, fibreMap]

/-- Base change along a weak map between point objects detects weakness of
the actual map on pullbacks of two fibrations. -/
theorem fibreMap_weak_iff_of_weak_baseChange {K L : SSet.{0}} (c : L ⟶ B) (b : K ⟶ L)
    [Fibration p] [Fibration q] [WeakEquivalence b] :
    WeakEquivalence (fibreMap p q f g h (b ≫ c) (b ≫ (c ≫ g)) (Category.assoc _ _ _)) ↔
      WeakEquivalence (fibreMap p q f g h c (c ≫ g) rfl) := by
  haveI := overPoint_weak p c b
  haveI := overPoint_weak q (c ≫ g) b
  rw [← weakEquivalence_postcomp_iff _ (overPoint q (c ≫ g) b),
    ← overPoint_natural]
  exact weakEquivalence_precomp_iff _ _

private theorem vertex_weak (i : Fin 2) :
    WeakEquivalence (SSet.stdSimplex.map (SimplexCategory.δ i) :
      (Δ[0] : SSet.{0}) ⟶ Δ[1]) := by
  let a : (Δ[0] : SSet.{0}) ⟶ Δ[1] :=
    SSet.const (DaggerNativeStandardSimplexContraction.firstVertex 1)
  let t := SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0})
  haveI : WeakEquivalence a := DaggerNativeFibrationWeakFromVertexFibres.first_vertex_weak 1
  have ha : a ≫ t = 𝟙 _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  haveI : WeakEquivalence t := weakEquivalence_of_precomp_of_fac ha
  exact weakEquivalence_of_postcomp_of_fac
    (show SSet.stdSimplex.map (SimplexCategory.δ i) ≫ t = 𝟙 (Δ[0] : SSet.{0}) from
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private abbrev point (z : B.obj (op ⦋0⦌)) : (Δ[0] : SSet.{0}) ⟶ B :=
  SSet.yonedaEquiv.symm z

/-- For actual Kan fibrations, changing the specified source vertex within
its component preserves and reflects weakness of the actual strict fiber map. -/
theorem fibreMap_weak_iff_of_component [Fibration p] [Fibration q]
    (z w : B.obj (op ⦋0⦌)) (hz : SSet.π₀.mk z = SSet.π₀.mk w) :
    WeakEquivalence (fibreMap p q f g h (point z) (point z ≫ g) rfl) ↔
      WeakEquivalence (fibreMap p q f g h (point w) (point w ≫ g) rfl) := by
  have hgen := (SSet.π₀.mk_eq_mk_iff z w).mp hz
  clear hz
  induction hgen with
  | rel z w he =>
      obtain ⟨e, h₀, h₁⟩ := he
      let c : (Δ[1] : SSet.{0}) ⟶ B := SSet.yonedaEquiv.symm e
      have hb (i : Fin 2) : point (B.δ i e) = SSet.stdSimplex.map (SimplexCategory.δ i) ≫ c :=
        (SSet.stdSimplex.map_comp_yonedaEquiv_symm (X := B) e _).symm
      subst z
      subst w
      have H (i : Fin 2) : WeakEquivalence
          (fibreMap p q f g h (point (B.δ i e)) (point (B.δ i e) ≫ g) rfl) ↔
            WeakEquivalence (fibreMap p q f g h c (c ≫ g) rfl) := by
        rw [hb]
        haveI := vertex_weak i
        simpa only [Category.assoc] using
          fibreMap_weak_iff_of_weak_baseChange p q f g h c
            (SSet.stdSimplex.map (SimplexCategory.δ i))
      exact (H 1).trans (H 0).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end

end DaggerModels.PartII.FibrationSquareComponentFibers
