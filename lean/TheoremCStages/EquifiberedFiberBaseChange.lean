import BisimplicialEquifibered
import SSetWeakPullbackComparison
import NativeFibrationWeakFromVertexFibres

/-!
# Fiber base change from an equifibered transition

A weak transition comparison into the strict pullback of a row fibration
induces a weak map after base change along any specified simplex. A weak
change of the simplex itself is then handled by right properness. Neither
the total nor the base transition is assumed weak.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.EquifiberedFiberBaseChange

noncomputable section

/-- A weak homotopy-cartesian transition remains weak on the strict
pullback at an arbitrary unchanged point object. -/
theorem fixedPoint_weak {X Y B D K : SSet.{0}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) [Fibration p] [Fibration q]
    (hc : WeakEquivalence (pullback.lift f p h.symm)) :
    WeakEquivalence
      (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
        p q f g h b (b ≫ g) rfl) := by
  let k := pullback.snd q g
  let t := pullback.fst q g
  let a : X ⟶ pullback q g := pullback.lift f p h.symm
  have ha : a ≫ k = p := by simp [a, k]
  have hat : a ≫ t = f := by simp [a, t]
  haveI : WeakEquivalence a := hc
  haveI : Fibration k := inferInstance
  let u := DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver p k a ha b
  haveI : WeakEquivalence u :=
    DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_weakEquivalence
      p k a ha b
  have square : IsPullback
      (pullback.fst k b ≫ t) (pullback.snd k b) q (b ≫ g) := by
    simpa only [k, t] using
      (IsPullback.of_hasPullback k b).paste_horiz
        (IsPullback.of_hasPullback q g)
  let e := square.isoPullback
  have he : u ≫ e.hom =
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
        p q f g h b (b ≫ g) rfl := by
    apply pullback.hom_ext
    · rw [Category.assoc, square.isoPullback_hom_fst,
        ← Category.assoc]
      rw [DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst,
        Category.assoc, hat,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst]
    · rw [Category.assoc, square.isoPullback_hom_snd,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
      simp [u, DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver]
  rw [← he]
  infer_instance

/-- A further weak change of the point simplex gives the actual
pullback comparison between distinct point objects. -/
theorem comparison_weak_of_transition {X Y B D K L : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) (d : L ⟶ D)
    (k : K ⟶ L) (hk : b ≫ g = k ≫ d)
    [Fibration p] [Fibration q] [WeakEquivalence k]
    (hc : WeakEquivalence (pullback.lift f p h.symm)) :
    WeakEquivalence
      (DaggerModels.PartII.SSetWeakPullbackComparison.comparison
        p q f g h b d k hk) := by
  let a := DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    p q f g h b (b ≫ g) rfl
  let t := DaggerModels.PartII.SSetWeakPullbackComparison.pointMap
    q (b ≫ g) d k hk
  haveI : WeakEquivalence a := fixedPoint_weak p q f g h b hc
  haveI : WeakEquivalence t :=
    DaggerModels.PartII.SSetWeakPullbackComparison.pointMap_weak
      q (b ≫ g) d k hk
  have ht : a ≫ t =
      DaggerModels.PartII.SSetWeakPullbackComparison.comparison
        p q f g h b d k hk := by
    apply pullback.hom_ext
    · simp only [Category.assoc, t,
        DaggerModels.PartII.SSetWeakPullbackComparison.pointMap_fst,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
        a, DaggerModels.PartII.SSetWeakPullbackComparison.comparison_fst]
    · simp only [Category.assoc, t,
        DaggerModels.PartII.SSetWeakPullbackComparison.pointMap_snd,
        a, DaggerModels.PartII.SSetWeakPullbackComparison.comparison_snd]
      rw [← Category.assoc,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
  rw [← ht]
  infer_instance

/-- Collapse of every standard simplex to the terminal simplex is weak. -/
theorem simplexCollapse_weak (n : SimplexCategory) :
    WeakEquivalence
      (SSet.stdSimplex.isTerminalObj₀.from
        (SSet.stdSimplex.{0}.obj n) :
          SSet.stdSimplex.{0}.obj n ⟶ (Δ[0] : SSet.{0})) := by
  induction n using SimplexCategory.rec with
  | _ k =>
      haveI : WeakEquivalence
          (SSet.const (DaggerNativeStandardSimplexContraction.firstVertex k) :
            (Δ[0] : SSet.{0}) ⟶ Δ[k]) :=
        DaggerNativeFibrationWeakFromVertexFibres.first_vertex_weak k
      have h :
          (SSet.const (DaggerNativeStandardSimplexContraction.firstVertex k) :
            (Δ[0] : SSet.{0}) ⟶ Δ[k]) ≫
              SSet.stdSimplex.isTerminalObj₀.from (Δ[k] : SSet.{0}) =
            𝟙 (Δ[0] : SSet.{0}) :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      exact weakEquivalence_of_precomp_of_fac h

/-- Every original standard-simplex operator is weak, with no choice
of a contraction or replacement of the operator. -/
theorem standardSimplexMap_weak {n m : SimplexCategory} (θ : n ⟶ m) :
    WeakEquivalence (SSet.stdSimplex.{0}.map θ :
      SSet.stdSimplex.{0}.obj n ⟶ SSet.stdSimplex.{0}.obj m) := by
  let cN := SSet.stdSimplex.isTerminalObj₀.from
    (SSet.stdSimplex.{0}.obj n)
  let cM := SSet.stdSimplex.isTerminalObj₀.from
    (SSet.stdSimplex.{0}.obj m)
  haveI : WeakEquivalence cN := simplexCollapse_weak n
  haveI : WeakEquivalence cM := simplexCollapse_weak m
  have h : SSet.stdSimplex.{0}.map θ ≫ cM = cN :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  haveI : WeakEquivalence (SSet.stdSimplex.{0}.map θ ≫ cM) := by
    rw [h]
    infer_instance
  exact weakEquivalence_of_postcomp (SSet.stdSimplex.{0}.map θ) cM

#print axioms fixedPoint_weak
#print axioms comparison_weak_of_transition
#print axioms standardSimplexMap_weak

end

end DaggerModels.PartII.EquifiberedFiberBaseChange
