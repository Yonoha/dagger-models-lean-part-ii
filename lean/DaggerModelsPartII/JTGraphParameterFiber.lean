import DaggerModelsPartII.JTGraphParameterInterpolation
import DaggerModelsPartII.JTNecklaceCylinderSimplexLift

/-!
# Interpolating lifts in a fixed reduced-cylinder fiber
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphParameterFiber

open GroupoidSimplex
open JTNecklaceEndpointCylinder JTCodiscreteParameterPairing JTGraphParameterInterpolation

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

/-- At a simplex of the ordered boundary the whole parameter collapses. -/
private theorem boundary_value (T : NecklaceCode) (k : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (a : B.obj q) (u : (J.obj k).obj q) :
    ((cylinder T).app k).app q ((endpointInclusion T).app q a, u) =
      ((boundary T).app k).app q a := by
  have h := congrFun (NatTrans.congr_app (isPushout T k).w q) (a, u)
  exact h

private theorem simplex_ext (k : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (s t : (J.obj k).obj q) (h : ∀ v, coord k q s v = coord k q t v) :
    s = t := by
  let e := (parameterCodiscreteIso.app k).app q
  apply (CategoryTheory.mono_iff_injective e.hom).mp inferInstance
  apply nerve.ext_of_isThin
  funext v
  exact Codiscrete.ext (h v)

/-- Vertexwise selection from a fixed cylinder fiber stays in that fiber
on the entire time product. The reference lift handles all simplices
whose horizontal coordinate is outside the ordered boundary. -/
theorem fiber_of_coordinates {X Y : SSet.{0}} {I : Type}
    (T : NecklaceCode) (k : SimplexCategory) (f : X ⟶ T.toSSet)
    (s : I → (X ⟶ J.obj k)) (t : X ⟶ J.obj k) (g : X ⟶ (value T).obj k)
    (h : ∀ i, lift f (s i) ≫ (cylinder T).app k = g)
    (ht : lift f t ≫ (cylinder T).app k = g)
    (p : X ⊗ Y ⟶ J.obj k)
    (hp : ∀ (q : SimplexCategoryᵒᵖ) (z : (X ⊗ Y).obj q) (v : Fin (q.unop.len + 1)),
      ∃ i, coord k q (p.app q z) v = coord k q ((s i).app q z.1) v) :
    lift (fst X Y ≫ f) p ≫ (cylinder T).app k = fst X Y ≫ g := by
  classical
  apply NatTrans.ext
  funext q
  induction q using Opposite.rec with | op q =>
  induction q using SimplexCategory.rec with | h d =>
    funext z
    let q := op ⦋d⦌
    change ((cylinder T).app k).app q (f.app q z.1, p.app q z) = g.app q z.1
    have h₀ : ((cylinder T).app k).app q (f.app q z.1, t.app q z.1) = g.app q z.1 :=
      congrFun (NatTrans.congr_app ht q) z.1
    by_cases hb : ∃ a : B.obj q, (endpointInclusion T).app q a = f.app q z.1
    · obtain ⟨a, ha⟩ := hb
      rw [← ha] at h₀ ⊢
      rw [boundary_value]
      exact (boundary_value T k q a (t.app q z.1)).symm.trans h₀
    · have hparam (i : I) : (s i).app q z.1 = t.app q z.1 := by
        have hi : ((cylinder T).app k).app q (f.app q z.1, (s i).app q z.1) =
            g.app q z.1 := congrFun (NatTrans.congr_app (h i) q) z.1
        obtain heq | ⟨a, ha⟩ :=
          JTNecklaceCylinderSimplexLift.equal_lifts_parameter_or_boundary T k d
            (f.app q z.1, (s i).app q z.1) (f.app q z.1, t.app q z.1)
            (hi.trans h₀.symm)
        · exact heq
        · exact (hb ⟨a, ha⟩).elim
      have hs : p.app q z = t.app q z.1 := by
        apply simplex_ext
        intro v
        obtain ⟨i, hi⟩ := hp q z v
        exact hi.trans (congrArg (fun u ↦ coord k q u v) (hparam i))
      rw [hs]
      exact h₀

/-- A finite family with the same exact cylinder image interpolates
over the entire codiscrete time parameter with that image. -/
theorem interpolate_fiber {X : SSet.{0}} (T : NecklaceCode) (k n : SimplexCategory)
    (f : X ⟶ T.toSSet) (s : Fin (n.len + 1) → (X ⟶ J.obj k))
    (g : X ⟶ (value T).obj k)
    (h : ∀ i, lift f (s i) ≫ (cylinder T).app k = g) :
    lift (fst X (J.obj n) ≫ f) (interpolate s) ≫ (cylinder T).app k =
      fst X (J.obj n) ≫ g := by
  refine fiber_of_coordinates T k f s (s 0) g h (h 0) (interpolate s) ?_
  intro q z v
  exact ⟨coord n q z.2 v, coord_interpolate s q z v⟩

end

end DaggerModels.PartII.JTGraphParameterFiber
