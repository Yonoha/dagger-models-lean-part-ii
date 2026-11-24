import RelativeCosliceRestrictionLifting
import OriginalAllPrefixBoundaryInvertibleLifting
import OriginalVertexCosliceLeftLifting

/-!
# The actual relative boundary target and its original suffix projection

The first projection is the base change of the coslice restriction in the
target simplicial set. Its composite with the boundary projection in the
source lifts every nonfinal horn. This proves inner filling of the actual
pullback target and reflects invertibility of its edges from their original
suffix images. No relative outer-horn filler is assumed here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalCosliceLeftLiftingProperty
open DaggerOriginalAllPrefixBoundaryProjectionLifting
open DaggerOriginalRelativeLeftTwoHornInverses
open DaggerOriginalRelativeInvertibleEdgeTargetLift
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalVertexCosliceLeftLifting
open DaggerOriginalRelativeCosliceRestrictionLifting
open DaggerNativeInnerHornFactorization

universe u

namespace DaggerOriginalRelativeBoundaryTargetLifting

noncomputable section

/-- Evaluate the actual relative target on its original source suffix. -/
def relativeTargetProjection {C D : SSet.{u}} (p : C ⟶ D) (k : ℕ)
    (f : C.obj (op ⦋k⦌)) : relativeBoundaryTarget p k f ⟶ C :=
  pullback.fst _ _ ≫ boundaryProjection k C

/-- The actual pullback projection lifts all nonfinal horns. -/
theorem relativeTargetFirst_hasLiftingProperty {C D : SSet.{u}} (p : C ⟶ D)
    (hD : innerHornFillers D) (k : ℕ) (f : C.obj (op ⦋k⦌))
    (n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (pullback.fst (boundaryJoinedMap p k)
        (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f))) := by
  haveI := coslice_hasLiftingProperty hD k n i hi (p.app (op ⦋k⦌) f)
  infer_instance

/-- The projection to the original source retains all nonfinal horn lifts. -/
theorem relativeTargetProjection_hasLiftingProperty {C D : SSet.{u}} (p : C ⟶ D)
    (hC : innerHornFillers C) (hD : innerHornFillers D) (k : ℕ)
    (f : C.obj (op ⦋k⦌)) (n : ℕ) (i : Fin (n + 2))
    (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (relativeTargetProjection p k f) := by
  haveI := relativeTargetFirst_hasLiftingProperty p hD k f n i hi
  haveI := boundaryProjection_hasLiftingProperty hC k n i hi
  dsimp [relativeTargetProjection]
  infer_instance

/-- The actual relative pullback target has inner-horn fillers. -/
theorem relativeTarget_innerHornFillers {C D : SSet.{u}} (p : C ⟶ D)
    (hC : innerHornFillers C) (hD : innerHornFillers D) (k : ℕ)
    (f : C.obj (op ⦋k⦌)) : innerHornFillers (relativeBoundaryTarget p k f) :=
  innerHornFillers_of_nonfinal_lifting (relativeTargetProjection p k f) hC
    (fun n i hi ↦ relativeTargetProjection_hasLiftingProperty p hC hD k f n i hi)

/-- Invertibility is reflected from the same original suffix edge. -/
theorem relativeTarget_reflects_invertible_edge {C D : SSet.{u}} (p : C ⟶ D)
    (hC : innerHornFillers C) (hD : innerHornFillers D) (k : ℕ)
    (f : C.obj (op ⦋k⦌))
    {a b : (relativeBoundaryTarget p k f).obj (op ⦋0⦌)} (e : SSet.Edge a b)
    (he : edgeIsInvertible C (e.map (relativeTargetProjection p k f)).edge) :
    edgeIsInvertible (relativeBoundaryTarget p k f) e.edge := by
  haveI := relativeTargetProjection_hasLiftingProperty p hC hD k f 1 0 (by decide)
  exact edgeIsInvertible_of_invertible_image (relativeTargetProjection p k f) hC e he

/-- Lift an invertible relative boundary edge to its actual prescribed coslice target. -/
theorem relativeCoslice_lift_invertible_image_edge_to_target {C D : SSet.{u}}
    (p : C ⟶ D) (hp : innerFibrations p) (hC : innerHornFillers C)
    (hD : innerHornFillers D) (k : ℕ) (f : C.obj (op ⦋k⦌))
    (b : (simplexCoslice ⦋k⦌ C f).obj (op ⦋0⦌))
    {x : (relativeBoundaryTarget p k f).obj (op ⦋0⦌)}
    (e : SSet.Edge x ((relativeCosliceRestriction p k f).app (op ⦋0⦌) b))
    (he : edgeIsInvertible C (e.map (relativeTargetProjection p k f)).edge) :
    ∃ a : (simplexCoslice ⦋k⦌ C f).obj (op ⦋0⦌),
      (relativeCosliceRestriction p k f).app (op ⦋0⦌) a = x ∧
        ∃ g : SSet.Edge a b,
          (relativeCosliceRestriction p k f).app (op ⦋1⦌) g.edge = e.edge ∧
            edgeIsInvertible (simplexCoslice ⦋k⦌ C f) g.edge := by
  haveI := relativeCosliceRestriction_hasLiftingProperty p hp k f 0 0 (by decide)
  haveI := relativeCosliceRestriction_hasLiftingProperty p hp k f 1 0 (by decide)
  exact lift_invertible_edge_to_target (relativeCosliceRestriction p k f)
    (relativeTarget_innerHornFillers p hC hD k f) b e
    (relativeTarget_reflects_invertible_edge p hC hD k f e he)

#print axioms relativeTarget_innerHornFillers
#print axioms relativeTarget_reflects_invertible_edge
#print axioms relativeCoslice_lift_invertible_image_edge_to_target

end

end DaggerOriginalRelativeBoundaryTargetLifting
