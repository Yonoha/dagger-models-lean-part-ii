import DaggerModelsPartII.JTFixedLiftSpaceInterleavedBoundaryMap
import DaggerModelsPartII.JTFixedLiftSpaceInterleavedRelative
import NativeBoundaryJoyalMappingWeak

/-!
# Boundary lifting for the original enlargement projection
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial MonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFixedLiftSpaceInterleavedTrivialFibration

open JTFixedLiftSpaceInterleaved JTFixedLiftSpaceTimeEquiv JTHigherInterleavedParameter
open JTFixedLiftSpaceInterleavedProjection JTFixedLiftSpaceInterleavedRelative
open JTFixedLiftSpaceTimeBoundaryChoices JTFixedLiftSpaceInterleavedBoundaryMap

noncomputable section

variable {A X Y : SSet.{u}} {k : ℕ} {i : A ⟶ (Δ[k] : SSet.{u})}
variable {t : A ⟶ X} {p : X ⟶ Y} {b : (Δ[k] : SSet.{u}) ⟶ Y}
variable (sq : CommSq t i p b)

private abbrev Fiber := (SSet.ihomToPullbackFiber sq : SSet.{u})

/-- All specified enlarged time faces lift at once along the same
projection to the original normalization space. -/
theorem projection_boundary_lifting [Fibration p] (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι (projection sq) := by
  constructor
  intro β v S
  obtain ⟨E, hP, hB⟩ := exists_extension_relative sq n (SSet.yonedaEquiv v)
    (boundaryMap sq β) (boundaryMap_over sq β) (boundaryMap_overlap sq β v S.w)
  have hE : ∀ {m : SimplexCategory} (j : m ⟶ ⦋n⦌)
      (hj : ¬ Function.Surjective j.toOrderHom),
      restrict sq j E = choice sq β j hj := by
    intro m j hj
    obtain ⟨a, ha, hb⟩ := exists_boundaryMap_operator sq β j hj
    apply Extension.ext
    change SSet.stdSimplex.map (mapTime ⦋k⦌ j) ≫ E.map = _
    rw [← ha, Category.assoc, hB, hb]
  let e : (Δ[n] : SSet.{u}) ⟶ extensionSpace sq := SSet.yonedaEquiv.symm E
  have he : SSet.yonedaEquiv e = E :=
    (SSet.yonedaEquiv (X := extensionSpace sq) (n := ⦋n⦌)).apply_symm_apply E
  refine CommSq.HasLift.mk' ⟨e, ?_, ?_⟩
  · apply NatTrans.ext
    funext q x
    induction q using Opposite.rec with
    | op m =>
      let j := SSet.stdSimplex.objEquiv x.val
      have hx : ¬ Function.Surjective j.toOrderHom := x.property
      have hx' : boundaryPoint j hx = x := Subtype.ext
        (SSet.stdSimplex.objEquiv.symm_apply_apply x.val)
      change e.app (op m) x.val = β.app (op m) x
      have hh : e.app (op m) (SSet.stdSimplex.objEquiv.symm j) =
          (extensionSpace sq).map j.op E := by
        rw [← SSet.stdSimplex.yonedaEquiv_map, ← SSet.yonedaEquiv_comp,
          SSet.yonedaEquiv_map_comp, he]
      change e.app (op m) x.val = _ at hh
      rw [hh]
      have H := hE j hx
      change (extensionSpace sq).map j.op E = β.app (op m) (boundaryPoint j hx) at H
      rwa [hx'] at H
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, he]
    apply (timeEquiv sq ⦋n⦌).injective
    apply Subtype.ext
    change timeMap sq ⦋n⦌ ((projection sq).app (op ⦋n⦌) E) =
      timeMap sq ⦋n⦌ (SSet.yonedaEquiv v)
    have h := project_timeMap sq E
    change timeMap sq ⦋n⦌ ((projection sq).app (op ⦋n⦌) E) = _ at h
    exact h.trans hP

/-- The exact enlargement projection is a Kan trivial fibration. -/
theorem projection_trivialFibration_std [Fibration p] :
    trivialFibrations SSet.{u} (projection sq) :=
  (DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_iff_trivialFibration _).mp
    (projection_boundary_lifting sq)

/-- The same conclusion with an arbitrary simplex-category object as
the original coefficient. -/
theorem projection_trivialFibration {k' : SimplexCategory}
    {i' : A ⟶ SSet.stdSimplex.{u}.obj k'} {b' : SSet.stdSimplex.{u}.obj k' ⟶ Y}
    (sq' : CommSq t i' p b') [Fibration p] :
    trivialFibrations SSet.{u} (projection sq') := by
  cases k' using SimplexCategory.rec with
  | _ j => exact projection_trivialFibration_std sq'

end

end DaggerModels.PartII.JTFixedLiftSpaceInterleavedTrivialFibration
