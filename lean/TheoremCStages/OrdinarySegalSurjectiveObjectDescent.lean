import DaggerModelsPartII.FibrationSquareComponentFibers
import NativeFibrewiseWeakRecognition

/-!
# Reflection of fiberwise weakness from a component-surjective base change

For two actual Kan fibrations over the same simplicial set, a weak map
after base change along a map surjective on components is already weak.
The base-change map itself need not be a weak equivalence. This is the
generic descent step needed for the all-vertex Segal comparison.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks (mapOver mapOver_fst)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalSurjectiveObjectDescent

noncomputable section

private theorem mapOver_weak_iff_component {X Y B : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (h : f ≫ q = p)
    [Fibration p] [Fibration q]
    (z w : B.obj (op ⦋0⦌)) (hz : SSet.π₀.mk z = SSet.π₀.mk w) :
    WeakEquivalence (mapOver p q f h (SSet.yonedaEquiv.symm z)) ↔
      WeakEquivalence (mapOver p q f h (SSet.yonedaEquiv.symm w)) := by
  have h' : p ≫ (𝟙 B) = f ≫ q := by rw [Category.comp_id, h]
  have H := FibrationSquareComponentFibers.fibreMap_weak_iff_of_component
    p q f (𝟙 B) h' z w hz
  simpa only [Category.comp_id] using H

private theorem iteratedBaseChange_weak_iff {X Y B A K : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y)
    (h : f ≫ q = p) (g : A ⟶ B) (a : K ⟶ A) :
    WeakEquivalence
        (mapOver (pullback.snd p g) (pullback.snd q g)
          (mapOver p q f h g) (by simp [mapOver]) a) ↔
      WeakEquivalence (mapOver p q f h (a ≫ g)) := by
  let p' := pullback.snd p g
  let q' := pullback.snd q g
  let f' := mapOver p q f h g
  have h' : f' ≫ q' = p' := by simp [f', p', q', mapOver]
  let sp : IsPullback
      (pullback.fst p' a ≫ pullback.fst p g)
      (pullback.snd p' a) p (a ≫ g) := by
    simpa only [p'] using
      (IsPullback.of_hasPullback p' a).paste_horiz
        (IsPullback.of_hasPullback p g)
  let sq : IsPullback
      (pullback.fst q' a ≫ pullback.fst q g)
      (pullback.snd q' a) q (a ≫ g) := by
    simpa only [q'] using
      (IsPullback.of_hasPullback q' a).paste_horiz
        (IsPullback.of_hasPullback q g)
  let ep := sp.isoPullback
  let eq := sq.isoPullback
  let m := mapOver p q f h (a ≫ g)
  let m' := mapOver p' q' f' h' a
  have he : m' ≫ eq.hom = ep.hom ≫ m := by
    apply pullback.hom_ext
    · calc
        (m' ≫ eq.hom) ≫ pullback.fst q (a ≫ g) =
            (m' ≫ pullback.fst q' a) ≫ pullback.fst q g := by
              rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc]
        _ = (pullback.fst p' a ≫ f') ≫ pullback.fst q g := by
              dsimp only [m']
              rw [mapOver_fst]
        _ = (pullback.fst p' a ≫ pullback.fst p g) ≫ f := by
              dsimp only [f']
              rw [Category.assoc, mapOver_fst, ← Category.assoc]
        _ = (ep.hom ≫ pullback.fst p (a ≫ g)) ≫ f := by
              rw [sp.isoPullback_hom_fst]
        _ = (ep.hom ≫ m) ≫ pullback.fst q (a ≫ g) := by
              simpa only [m, Category.assoc] using
                (congrArg (fun k ↦ ep.hom ≫ k) (mapOver_fst p q f h (a ≫ g))).symm
    · calc
        (m' ≫ eq.hom) ≫ pullback.snd q (a ≫ g) =
            m' ≫ pullback.snd q' a := by
              rw [Category.assoc, sq.isoPullback_hom_snd]
        _ = pullback.snd p' a := by simp [m', mapOver]
        _ = ep.hom ≫ pullback.snd p (a ≫ g) := sp.isoPullback_hom_snd.symm
        _ = (ep.hom ≫ m) ≫ pullback.snd q (a ≫ g) := by
              rw [Category.assoc]
              simp [m, mapOver]
  constructor
  · intro hw
    have : WeakEquivalence (m' ≫ eq.hom) := inferInstance
    rw [he] at this
    exact (weakEquivalence_precomp_iff ep.hom _).mp this
  · intro hw
    have : WeakEquivalence (ep.hom ≫ m) := inferInstance
    rw [← he] at this
    exact (weakEquivalence_postcomp_iff _ eq.hom).mp this

/-- A component-surjective base change reflects an actual weak map between
Kan fibrations over the same unchanged base. -/
theorem weak_of_component_surjective_baseChange {X Y B A : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y)
    (h : f ≫ q = p) [Fibration p] [Fibration q]
    (g : A ⟶ B) (hg : Function.Surjective (SSet.mapπ₀ g))
    (hf : WeakEquivalence (mapOver p q f h g)) : WeakEquivalence f := by
  let p' := pullback.snd p g
  let q' := pullback.snd q g
  let f' := mapOver p q f h g
  have h' : f' ≫ q' = p' := by simp [f', p', q', mapOver]
  haveI : Fibration p' := inferInstance
  haveI : Fibration q' := inferInstance
  have hfa := (DaggerNativeFibrewiseWeakRecognition.weak_iff_vertex_base_changes
    p' q' f' h').mp hf
  apply DaggerNativeFibrewiseWeakRecognition.weak_of_vertex_base_changes p q f h
  intro b
  let w := SSet.yonedaEquiv b
  obtain ⟨u, hu⟩ := hg (SSet.π₀.mk w)
  obtain ⟨z, rfl⟩ := SSet.π₀.mk_surjective u
  let a : (Δ[0] : SSet.{0}) ⟶ A := SSet.yonedaEquiv.symm z
  have hz : SSet.π₀.mk (SSet.yonedaEquiv (a ≫ g)) = SSet.π₀.mk w := by
    rw [SSet.yonedaEquiv_comp, ← SSet.mapπ₀_mk]
    simpa only [a, Equiv.apply_symm_apply] using hu
  have ha : WeakEquivalence (mapOver p q f h (a ≫ g)) :=
    (iteratedBaseChange_weak_iff p q f h g a).mp (hfa a)
  have hcomp := mapOver_weak_iff_component p q f h
    (SSet.yonedaEquiv (a ≫ g)) w hz
  have hpoint : SSet.yonedaEquiv.symm (SSet.yonedaEquiv (a ≫ g)) = a ≫ g :=
    SSet.yonedaEquiv.symm_apply_apply (a ≫ g)
  have htarget : SSet.yonedaEquiv.symm w = b :=
    SSet.yonedaEquiv.symm_apply_apply b
  rw [hpoint, htarget] at hcomp
  exact hcomp.mp ha

#print axioms weak_of_component_surjective_baseChange

end

end DaggerModels.PartII.OrdinarySegalSurjectiveObjectDescent
