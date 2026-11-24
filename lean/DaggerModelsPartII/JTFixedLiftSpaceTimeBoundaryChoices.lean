import DaggerModelsPartII.JTFixedLiftSpaceInterleavedProjection
import TopCatModelCategory.SSet.Boundary

/-!
# The original simplicial boundary data for the enlargement space
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory

universe u

namespace DaggerModels.PartII.JTFixedLiftSpaceTimeBoundaryChoices

open JTFixedLiftSpaceInterleaved JTFixedLiftSpaceInterleavedProjection
open JTFixedLiftSpaceTimeEquiv JTHigherInterleavedParameter

noncomputable section

variable {A X Y : SSet.{u}} {k : SimplexCategory}
variable {i : A ⟶ SSet.stdSimplex.{u}.obj k} {t : A ⟶ X} {p : X ⟶ Y}
variable {b : SSet.stdSimplex.{u}.obj k ⟶ Y}
variable (sq : CommSq t i p b)

private abbrev Fiber := (SSet.ihomToPullbackFiber sq : SSet.{u})

variable {n : ℕ}
variable (β : (SSet.boundary n : SSet.{u}) ⟶ extensionSpace sq)

def boundaryPoint {m : SimplexCategory} (j : m ⟶ ⦋n⦌)
    (hj : ¬ Function.Surjective j.toOrderHom) :
    (SSet.boundary.{u} n).toSSet.obj (op m) :=
  ⟨SSet.stdSimplex.objEquiv.symm j, hj⟩

/-- Evaluate an actual simplicial boundary at any time operator landing
in the boundary. -/
def choice {m : SimplexCategory} (j : m ⟶ ⦋n⦌)
    (hj : ¬ Function.Surjective j.toOrderHom) : Extension sq m :=
  β.app (op m) (boundaryPoint j hj)

theorem choice_comp {l m : SimplexCategory} (a : l ⟶ m) (j : m ⟶ ⦋n⦌)
    (hj : ¬ Function.Surjective j.toOrderHom)
    (haj : ¬ Function.Surjective (a ≫ j).toOrderHom) :
    choice sq β (a ≫ j) haj = restrict sq a (choice sq β j hj) := by
  have h : (SSet.boundary.{u} n).toSSet.map a.op (boundaryPoint j hj) =
      boundaryPoint (a ≫ j) haj := Subtype.ext rfl
  have hn := congrFun (β.naturality a.op) (boundaryPoint j hj)
  change β.app (op l) ((SSet.boundary.{u} n).toSSet.map a.op (boundaryPoint j hj)) =
    restrict sq a (choice sq β j hj) at hn
  rw [h] at hn
  exact hn

/-- The boundary square determines the whole product-prism restriction
of each specified extension. -/
theorem choice_prism (v : (Δ[n] : SSet.{u}) ⟶ Fiber sq)
    (h : β ≫ projection sq = (SSet.boundary n).ι ≫ v)
    {m : SimplexCategory} (j : m ⟶ ⦋n⦌)
    (hj : ¬ Function.Surjective j.toOrderHom) :
    prism k m ≫ (choice sq β j hj).map =
      (SSet.stdSimplex.obj k ◁ SSet.stdSimplex.map j) ≫ timeMap sq ⦋n⦌ (SSet.yonedaEquiv v) := by
  have hp := congrArg (fun g : (SSet.boundary n : SSet.{u}) ⟶ Fiber sq ↦
    g.app (op m) (boundaryPoint j hj)) h
  change (projection sq).app (op m) (choice sq β j hj) =
    v.app (op m) (SSet.stdSimplex.objEquiv.symm j) at hp
  have hv : v.app (op m) (SSet.stdSimplex.objEquiv.symm j) =
      (Fiber sq).map j.op (SSet.yonedaEquiv v) := by
    apply SSet.yonedaEquiv.symm.injective
    rw [SSet.yonedaEquiv_symm_map, Equiv.symm_apply_apply]
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  have ht := project_timeMap sq (choice sq β j hj)
  change timeMap sq m ((projection sq).app (op m) (choice sq β j hj)) = _ at ht
  rw [hp, hv, timeMap_map] at ht
  exact ht.symm

end

end DaggerModels.PartII.JTFixedLiftSpaceTimeBoundaryChoices
