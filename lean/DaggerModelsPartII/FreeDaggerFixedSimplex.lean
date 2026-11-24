import DaggerModels.FreeDaggerCofibration
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Fixed simplices in the concrete free dagger pushout

The two copies of a simplicial set in its free dagger completion meet
exactly in the vertex image. A fixed simplex therefore comes from a
vertex, in every dimension and without a nondegeneracy hypothesis.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory DaggerModels

universe u

namespace DaggerModels.PartII.FreeDaggerFixedSimplex

noncomputable section

/-- Every fixed simplex in the concrete free dagger completion belongs
to the first copy of the common vertex image. -/
theorem fixed_mem_vertex_inl (A : SSet.{u}) (n : ℕ)
    (x : (FreeDaggerPushout.underlying A) _⦋n⦌)
    (hfix : (FreeDaggerPushout.obj A).daggerSimplex x = x) :
    ∃ v : A.obj (op ⦋0⦌),
      (SSetVertices.inclusion A ≫ FreeDaggerPushout.inl A).app (op ⦋n⦌) v = x := by
  obtain (⟨a, rfl⟩ | ⟨b, rfl⟩) := FreeDaggerPushout.exists_copy A (op ⦋n⦌) x
  · rw [FreeDaggerPushout.daggerSimplex_inl] at hfix
    obtain ⟨v, ha, _⟩ :=
      (FreeDaggerPushout.inl_eq_inr_iff A (op ⦋n⦌) a _).1 hfix.symm
    refine ⟨v, ?_⟩
    change (FreeDaggerPushout.inl A).app (op ⦋n⦌)
      ((SSetVertices.inclusion A).app (op ⦋n⦌) v) =
        (FreeDaggerPushout.inl A).app (op ⦋n⦌) a
    rw [ha]
  · rw [FreeDaggerPushout.daggerSimplex_inr] at hfix
    obtain ⟨v, ha, _⟩ :=
      (FreeDaggerPushout.inl_eq_inr_iff A (op ⦋n⦌) _ b).1 hfix
    refine ⟨v, ?_⟩
    change (FreeDaggerPushout.inl A).app (op ⦋n⦌)
      ((SSetVertices.inclusion A).app (op ⦋n⦌) v) =
        (FreeDaggerPushout.inr A).app (op ⦋n⦌) b
    rw [ha]
    exact hfix

/-- A dagger-compatible product presentation carries a fixed simplex to
the vertex image in its free-dagger first coordinate. The parameter's
dagger may be arbitrary. -/
theorem tensor_fixed_mem_vertices (A : SSet.{u}) (Y K : DaggerSSet.{u})
    (F : Y.toSSet ≅ FreeDaggerPushout.underlying A ⊗ K.toSSet)
    (hδ : F.hom ≫
      ((FreeDaggerPushout.obj A).dagger ⊗ₘ K.dagger) =
        Y.dagger ≫ SSet.opFunctor.map F.hom)
    (n : ℕ) (x : Y.toSSet _⦋n⦌)
    (hfix : Y.daggerSimplex x = x) :
    ∃ (v : A.obj (op ⦋0⦌)) (ξ : K.toSSet.obj (op ⦋n⦌)),
      F.hom.app (op ⦋n⦌) x =
        ((SSetVertices.inclusion A ≫ FreeDaggerPushout.inl A).app
          (op ⦋n⦌) v, ξ) := by
  let y := F.hom.app (op ⦋n⦌) x
  have hmap := congrFun (NatTrans.congr_app hδ (op ⦋n⦌)) x
  have hmap' := congrArg
    (fun z : (FreeDaggerPushout.underlying A ⊗ K.toSSet).op.obj (op ⦋n⦌) ↦
      SSet.opObjEquiv z) hmap
  have hpair :
      ((FreeDaggerPushout.obj A).daggerSimplex y.1,
        K.daggerSimplex y.2) =
        F.hom.app (op ⦋n⦌) (Y.daggerSimplex x) := by
    change
      ((FreeDaggerPushout.obj A).daggerSimplex y.1,
        K.daggerSimplex y.2) =
        F.hom.app (op ⦋n⦌) (Y.daggerSimplex x) at hmap'
    exact hmap'
  rw [hfix] at hpair
  have hfirst : (FreeDaggerPushout.obj A).daggerSimplex y.1 = y.1 :=
    congrArg Prod.fst hpair
  obtain ⟨v, hv⟩ := fixed_mem_vertex_inl A n y.1 hfirst
  refine ⟨v, y.2, ?_⟩
  change y = ((SSetVertices.inclusion A ≫ FreeDaggerPushout.inl A).app
    (op ⦋n⦌) v, y.2)
  exact Prod.ext hv.symm rfl

end

end DaggerModels.PartII.FreeDaggerFixedSimplex
