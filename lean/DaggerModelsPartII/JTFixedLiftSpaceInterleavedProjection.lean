import DaggerModelsPartII.JTFixedLiftSpaceInterleaved
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv

/-!
# Restriction of enlargement choices to the original normalization space
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFixedLiftSpaceInterleavedProjection

open JTFixedLiftSpaceInterleaved JTFixedLiftSpaceTimeEquiv JTHigherInterleavedParameter

noncomputable section

variable {A X Y : SSet.{u}} {k : SimplexCategory} {i : A ⟶ SSet.stdSimplex.{u}.obj k}
variable {t : A ⟶ X} {p : X ⟶ Y} {b : SSet.stdSimplex.{u}.obj k ⟶ Y}
variable (sq : CommSq t i p b)

private def projectedLift {n : SimplexCategory} (E : Extension sq n) :
    TimeLift sq n :=
  ⟨prism k n ≫ E.map, E.stationary, prism_over sq E⟩

private def project {n : SimplexCategory} (E : Extension sq n) :
    (SSet.ihomToPullbackFiber sq).obj (op n) :=
  (timeEquiv sq n).symm (projectedLift sq E)

theorem project_timeMap {n : SimplexCategory} (E : Extension sq n) :
    timeMap sq n (project sq E) = prism k n ≫ E.map :=
  congrArg Subtype.val ((timeEquiv sq n).apply_symm_apply (projectedLift sq E))

/-- Every enlargement retains the original time simplex, with exact
naturality in all time faces and degeneracies. -/
def projection : extensionSpace sq ⟶ (SSet.ihomToPullbackFiber sq : SSet.{u}) where
  app _ := project sq
  naturality {m n} j := by
    funext E
    change project sq (restrict sq j.unop E) =
      (SSet.ihomToPullbackFiber sq : SSet.{u}).map j (project sq E)
    apply (timeEquiv sq n.unop).injective
    apply Subtype.ext
    change timeMap sq n.unop (project sq (restrict sq j.unop E)) =
      timeMap sq n.unop ((SSet.ihomToPullbackFiber sq : SSet.{u}).map j (project sq E))
    have ht := timeMap_map sq j.unop (project sq E)
    change timeMap sq n.unop
      ((SSet.ihomToPullbackFiber sq : SSet.{u}).map j (project sq E)) = _ at ht
    rw [project_timeMap, ht, project_timeMap, restrict_prism]

/-- Any entire original time family admits an enlargement when the
original endpoint arrow is a fibration. -/
theorem projection_surjective [Fibration p] (n : SimplexCategory) :
    Function.Surjective ((projection sq).app (op n)) := by
  intro v
  obtain ⟨E, hE⟩ := exists_extension sq n (timeMap sq n v)
    (timeMap_conditions sq n v).2 (timeMap_conditions sq n v).1
  refine ⟨E, ?_⟩
  change project sq E = v
  apply (timeEquiv sq n).injective
  apply Subtype.ext
  change timeMap sq n (project sq E) = timeMap sq n v
  rw [project_timeMap, hE]

end

end DaggerModels.PartII.JTFixedLiftSpaceInterleavedProjection
