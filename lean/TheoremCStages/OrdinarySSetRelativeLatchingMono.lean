import OrdinarySSetLatchingMono
import DaggerModelsPartII.ReedyMaps
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Relative latching maps of ordinary simplicial monomorphisms

The absolute latching comparison is the inclusion of degenerate simplices.
A simplicial monomorphism reflects degeneracy, so its absolute latching
square is a pullback. The actual relative pushout map is therefore monic.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySSetRelativeLatchingMono

noncomputable section

/-- The absolute latching square of a simplicial monomorphism is a pullback
of the actual sets of degenerate simplices. -/
theorem latching_square_pullback {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f]
    (n : ℕ) :
    IsPullback ((latchingComparison n).app X) ((latchingFunctor n).map f)
      (f.app (op ⦋n⦌)) ((latchingComparison n).app Y) := by
  have hi : Mono ((latchingComparison n).app X) :=
    OrdinarySSetLatchingMono.latchingComparison_mono X n
  have hk : Mono ((latchingComparison n).app Y) :=
    OrdinarySSetLatchingMono.latchingComparison_mono Y n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨((latchingComparison n).naturality f).symm, ?_, ?_⟩
  · intro u v huv
    exact (mono_iff_injective _).mp hi huv.1
  · intro x v hv
    have hdegY : (f.app (op ⦋n⦌)) x ∈ Y.degenerate n := by
      rw [← OrdinarySSetLatchingMono.latchingComparison_range Y n]
      exact ⟨v, hv.symm⟩
    have hdegX : x ∈ X.degenerate n :=
      (SSet.degenerate_iff_of_mono f x).1 hdegY
    have hrange : x ∈ Set.range ((latchingComparison n).app X) := by
      rw [OrdinarySSetLatchingMono.latchingComparison_range X n]
      exact hdegX
    obtain ⟨u, hu⟩ := hrange
    refine ⟨u, hu, ?_⟩
    apply (mono_iff_injective _).mp hk
    calc
      ((latchingComparison n).app Y) (((latchingFunctor n).map f) u) =
          (f.app (op ⦋n⦌)) (((latchingComparison n).app X) u) :=
        congrFun ((latchingComparison n).naturality f) u
      _ = (f.app (op ⦋n⦌)) x := by rw [hu]
      _ = ((latchingComparison n).app Y) v := hv

/-- Every actual relative latching map of an ordinary simplicial-set
monomorphism is injective, at every simplicial degree. -/
theorem relativeLatchingMap_mono {X Y : SSet.{0}} (f : X ⟶ Y)
    [Mono f] (n : ℕ) : Mono (relativeLatchingMap n f) := by
  have hi : Mono ((latchingComparison n).app X) :=
    OrdinarySSetLatchingMono.latchingComparison_mono X n
  have hk : Mono ((latchingComparison n).app Y) :=
    OrdinarySSetLatchingMono.latchingComparison_mono Y n
  have hf : Mono (f.app (op ⦋n⦌)) :=
    (NatTrans.mono_iff_mono_app f).mp inferInstance (op ⦋n⦌)
  have hleft : pushout.inl ((latchingComparison n).app X)
        ((latchingFunctor n).map f) ≫ relativeLatchingMap n f =
      f.app (op ⦋n⦌) := pushout.inl_desc _ _ _
  have hright : pushout.inr ((latchingComparison n).app X)
        ((latchingFunctor n).map f) ≫ relativeLatchingMap n f =
      (latchingComparison n).app Y := pushout.inr_desc _ _ _
  exact Types.mono_of_isPushout_of_isPullback
    (IsPushout.of_hasPushout ((latchingComparison n).app X)
      ((latchingFunctor n).map f))
    (latching_square_pullback f n) hleft hright
    (fun a b _ _ hab ↦ (mono_iff_injective _).mp hk hab)

#print axioms latching_square_pullback
#print axioms relativeLatchingMap_mono

end
end DaggerModels.PartII.OrdinarySSetRelativeLatchingMono
