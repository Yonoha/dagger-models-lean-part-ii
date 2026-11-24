import NativeFibrewiseWeakRecognition
import NativeSSetFibrationSquareFibreWeak

/-! Recognition of weakness of the original map in an endpoint-fibration square. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FibrationSquareWeakRecognition

open DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open DaggerNativeSSetFibrationSquareFibreWeak

universe u

noncomputable section

/-- In a square between Kan fibrations, a weak base map and weak maps on
all vertex fibers imply that the original total map is weak. -/
theorem weak_of_weak_base_and_vertex_fibers {X Y B D : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) [Fibration p] [Fibration q] [WeakEquivalence g]
    (hf : ∀ b : (Δ[0] : SSet.{u}) ⟶ B,
      WeakEquivalence (fibreMap p q f g h b (b ≫ g) rfl)) :
    WeakEquivalence f := by
  let k := pullback.snd q g
  let t := pullback.fst q g
  let a : X ⟶ pullback q g := pullback.lift f p h.symm
  have ha : a ≫ k = p := pullback.lift_snd _ _ _
  have hat : a ≫ t = f := pullback.lift_fst _ _ _
  haveI : Fibration k := inferInstance
  haveI : WeakEquivalence t :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback q g)
  haveI : WeakEquivalence a := by
    apply DaggerNativeFibrewiseWeakRecognition.weak_of_vertex_base_changes p k a ha
    intro b
    let u := mapOver p k a ha b
    have sq : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b) q (b ≫ g) :=
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
    have hcal : u ≫ sq.isoPullback.hom = fibreMap p q f g h b (b ≫ g) rfl := by
      apply pullback.hom_ext
      · rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc]
        rw [mapOver_fst, Category.assoc, hat, fibreMap_fst]
      · rw [Category.assoc, sq.isoPullback_hom_snd, fibreMap_snd]
        simp [u, mapOver]
    haveI : WeakEquivalence (fibreMap p q f g h b (b ≫ g) rfl) := hf b
    exact weakEquivalence_of_postcomp_of_fac hcal
  rw [← hat]
  infer_instance

end

end DaggerModels.PartII.FibrationSquareWeakRecognition
