import NativeSSetFibrationSquareFibreWeak

/-!
# The actual fiber map of a fibrant relative corner

The corner is the literal comparison to the pullback of the base square.
Its base change followed by the standard pullback-pasting isomorphism is
exactly the original fiber map. No weak-equivalence hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.KanFibrationCornerFibre

open DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open DaggerNativeSSetFibrationSquareFibreWeak

noncomputable section

/-- The literal relative comparison for the given total/base square. -/
def corner {X Y A B : SSet.{0}} (p : X ⟶ A) (q : Y ⟶ B)
    (f : X ⟶ Y) (g : A ⟶ B) (h : p ≫ g = f ≫ q) : X ⟶ pullback q g :=
  pullback.lift f p h.symm

/-- A Kan-fibrant relative corner gives the original Kan-fibrant fiber
map at the exact original point and its specified image. -/
theorem fibreMap_fibration {X Y A B K : SSet.{0}} (p : X ⟶ A) (q : Y ⟶ B)
    (f : X ⟶ Y) (g : A ⟶ B) (h : p ≫ g = f ≫ q)
    (b : K ⟶ A) (d : K ⟶ B) (hb : b ≫ g = d)
    [Fibration (corner p q f g h)] :
    Fibration (fibreMap p q f g h b d hb) := by
  let k := pullback.snd q g
  let t := pullback.fst q g
  let c := corner p q f g h
  have hc : c ≫ k = p := pullback.lift_snd _ _ _
  let u := mapOver p k c hc b
  have : Fibration u := by
    apply (fibration_iff _).mpr
    exact (fibrations SSet.{0}).of_isPullback
      (mapOver_isPullback p k c hc b).flip ((fibration_iff _).mp inferInstance)
  have sq : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b) q d := by
    simpa only [k, t, hb] using
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
  let e := sq.isoPullback
  have he : u ≫ e.hom = fibreMap p q f g h b d hb := by
    apply pullback.hom_ext
    · rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc,
        mapOver_fst, Category.assoc]
      rw [show c ≫ t = f from pullback.lift_fst _ _ _, fibreMap_fst]
    · rw [Category.assoc, sq.isoPullback_hom_snd, fibreMap_snd]
      dsimp only [u, mapOver]
      exact pullback.lift_snd _ _ _
  rw [← he]
  infer_instance

#print axioms fibreMap_fibration

end
end DaggerModels.PartII.KanFibrationCornerFibre
