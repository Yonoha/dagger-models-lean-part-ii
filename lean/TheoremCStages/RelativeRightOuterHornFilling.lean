import RelativeRightOuterHornData

/-!
# Original right outer horns lifted through an actual inner fibration

The prescribed simplex in the base determines an edge of the relative
boundary target. Its invertible original suffix edge lifts through the
relative coslice restriction. The lifted joined edge reconstructs the
original horn and retains the full prescribed base simplex.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalInnerHornFillers DaggerOriginalSimplexCoslice
open DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalRightOuterHornInclusions DaggerOriginalRightOuterHornData
open DaggerOriginalRightOuterHornFilling
open DaggerOriginalRelativeCosliceRestrictionLifting
open DaggerOriginalRelativeBoundaryTargetLifting
open DaggerOriginalRelativeRightOuterHornData
open DaggerNativeInnerHornFactorization

universe u

namespace DaggerOriginalRelativeRightOuterHornFilling

noncomputable section

/-- The relative right outer horn filler retains the exact prescribed base simplex.
No absolute outer-horn lifting property is assumed for the inner fibration. -/
theorem right_outer_horn_filler_over {C D : SSet.{u}} (p : C ⟶ D)
    (hp : innerFibrations p) (hC : innerHornFillers C) (hD : innerHornFillers D)
    (k : ℕ) (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ C)
    (μD : (Δ[k + 2] : SSet.{u}) ⟶ D)
    (w : φ ≫ p = Λ[k + 2, Fin.last (k + 2)].ι ≫ μD)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (rightOuterLastEdgeInclusion k ≫ φ))) :
    ∃ μC : (Δ[k + 2] : SSet.{u}) ⟶ C,
      φ = Λ[k + 2, Fin.last (k + 2)].ι ≫ μC ∧ μC ≫ p = μD := by
  let f := rightOuterPrefix k φ
  let b := rightOuterCosliceVertex k φ
  obtain ⟨a, e, hboundaryEdge, hbaseEdge⟩ :=
    relative_right_outer_boundary_edge p k φ μD w
  have he' : edgeIsInvertible C
      (e.map (relativeTargetProjection p k f)).edge := by
    have himage : (e.map (relativeTargetProjection p k f)).edge =
        ((rightOuterBoundaryEdge k φ).map (boundaryProjection k C)).edge := by
      change (boundaryProjection k C).app (op ⦋1⦌)
        ((pullback.fst (boundaryJoinedMap p k)
          (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f))).app (op ⦋1⦌)
            e.edge) =
          (boundaryProjection k C).app (op ⦋1⦌)
            (rightOuterBoundaryEdge k φ).edge
      exact congrArg ((boundaryProjection k C).app (op ⦋1⦌)) hboundaryEdge
    rw [himage, rightOuterBoundaryEdge_image]
    exact he
  obtain ⟨aC, haC, g, hg, _⟩ :=
    relativeCoslice_lift_invertible_image_edge_to_target p hp hC hD k f b e he'
  have hboundary : (cosliceBoundaryRestriction k C f).app (op ⦋1⦌) g.edge =
      (rightOuterBoundaryEdge k φ).edge := by
    have h := congrArg (fun x ↦
      (pullback.fst (boundaryJoinedMap p k)
        (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f))).app (op ⦋1⦌) x) hg
    change ((relativeCosliceRestriction p k f ≫ pullback.fst _ _).app (op ⦋1⦌)
      g.edge) = _ at h
    have hf : relativeCosliceRestriction p k f ≫ pullback.fst _ _ =
        cosliceBoundaryRestriction k C f := pullback.lift_fst _ _ _
    have hproject := congrArg (fun t ↦ t.app (op ⦋1⦌) g.edge) hf
    exact hproject.symm.trans (h.trans hboundaryEdge)
  let μC := rightOuterSimplexFromEdge k φ g
  have hμhorn : φ = Λ[k + 2, Fin.last (k + 2)].ι ≫ μC :=
    rightOuterSimplexFromEdge_horn k φ g hboundary
  have hbase : ((cosliceMap p ⦋k⦌ f).app (op ⦋1⦌) g.edge).val =
      SSet.yonedaEquiv μD := by
    have h := congrArg (fun x ↦
      (pullback.snd (boundaryJoinedMap p k)
        (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f))).app (op ⦋1⦌) x) hg
    have hv := congrArg Subtype.val h
    change ((relativeCosliceRestriction p k f ≫ pullback.snd _ _).app (op ⦋1⦌)
      g.edge).val = _ at hv
    have hf : relativeCosliceRestriction p k f ≫ pullback.snd _ _ =
        cosliceMap p ⦋k⦌ f := pullback.lift_snd _ _ _
    have hproject := congrArg (fun t ↦ (t.app (op ⦋1⦌) g.edge).val) hf
    exact hproject.symm.trans (hv.trans hbaseEdge)
  refine ⟨μC, hμhorn, ?_⟩
  apply (SSet.yonedaEquiv (X := D) (n := ⦋k + 2⦌)).injective
  rw [SSet.yonedaEquiv_comp]
  dsimp only [μC, rightOuterSimplexFromEdge]
  rw [Equiv.apply_symm_apply]
  exact hbase

#print axioms right_outer_horn_filler_over

end

end DaggerOriginalRelativeRightOuterHornFilling
