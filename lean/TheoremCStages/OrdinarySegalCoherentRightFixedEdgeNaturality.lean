import OrdinarySegalMappingTargetSquares
import OrdinarySegalCoherentRightFixedTriangle
import OrdinarySegalCoherentFixedEdgeNaturality

/-!
# Whole target maps on the original last-edge-fixed triangles and right horns

The original coherent edge is postcomposed in the actual restriction.
The two pullback maps keep its directed simplex unit and fixed zero-simplex.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedEdgeNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentRightOuterHorn
open OrdinarySegalMappingTargetSquares (pre_post)
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

theorem hornRestriction_post {W V : Space} (f : W ⟶ V) :
    hornRestriction W ≫
        diagramMappingPostcomp (discrete.obj (Λ[2, Fin.last 2] : SSet.{0})) f =
      diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f ≫ hornRestriction V :=
  pre_post _ f

theorem lastEdgeRestriction_post {W V : Space} (f : W ⟶ V) :
    lastEdgeRestriction W ≫ diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f =
      diagramMappingPostcomp (discrete.obj (Λ[2, Fin.last 2] : SSet.{0})) f ≫
        lastEdgeRestriction V :=
  pre_post _ f

theorem fullLastEdge_post {W V : Space} (f : W ⟶ V) :
    (hornRestriction W ≫ lastEdgeRestriction W) ≫
        diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f =
      diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f ≫
        (hornRestriction V ≫ lastEdgeRestriction V) := by
  rw [Category.assoc, lastEdgeRestriction_post, ← Category.assoc,
    hornRestriction_post, Category.assoc]

/-- The whole last-edge-fixed triangle transforms by original mapping postcomposition. -/
def fixedFullMap {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ⟶
      pullback (hornRestriction V ≫ lastEdgeRestriction V)
        (coherentEdge V (postCoherent f H)) :=
  pullback.map _ _ _ _
    (diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f) (𝟙 _)
    (diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f)
    (fullLastEdge_post f)
    (by simpa only [Category.id_comp] using
      OrdinarySegalCoherentEdgeNaturality.coherentEdge_post f H)

/-- The same target map transforms the original fixed-last-edge horn. -/
def fixedHornMap {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (lastEdgeRestriction W) (coherentEdge W H) ⟶
      pullback (lastEdgeRestriction V) (coherentEdge V (postCoherent f H)) :=
  pullback.map _ _ _ _
    (diagramMappingPostcomp (discrete.obj (Λ[2, Fin.last 2] : SSet.{0})) f) (𝟙 _)
    (diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f)
    (lastEdgeRestriction_post f)
    (by simpa only [Category.id_comp] using
      OrdinarySegalCoherentEdgeNaturality.coherentEdge_post f H)

theorem fixedFullMap_fst {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedFullMap f H ≫ pullback.fst
        (hornRestriction V ≫ lastEdgeRestriction V) (coherentEdge V (postCoherent f H)) =
      pullback.fst (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f := by
  simp only [fixedFullMap, pullback.map, pullback.lift_fst]

theorem fixedHornMap_fst {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedHornMap f H ≫ pullback.fst
        (lastEdgeRestriction V) (coherentEdge V (postCoherent f H)) =
      pullback.fst (lastEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPostcomp (discrete.obj (Λ[2, Fin.last 2] : SSet.{0})) f := by
  simp only [fixedHornMap, pullback.map, pullback.lift_fst]

theorem restriction_fst (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedRestriction W H ≫ pullback.fst (lastEdgeRestriction W) (coherentEdge W H) =
      pullback.fst (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
        hornRestriction W :=
  DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst _ _ _ _ _

/-- The original full-triangle-to-horn restriction is natural in whole target maps. -/
theorem fixedRestriction_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedRestriction W H ≫ fixedHornMap f H =
      fixedFullMap f H ≫ fixedRestriction V (postCoherent f H) := by
  apply pullback.hom_ext
  · calc
      (fixedRestriction W H ≫ fixedHornMap f H) ≫ _ =
          pullback.fst (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
            hornRestriction W ≫
              diagramMappingPostcomp (discrete.obj (Λ[2, Fin.last 2] : SSet.{0})) f := by
        rw [Category.assoc, fixedHornMap_fst, ← Category.assoc, restriction_fst,
          Category.assoc]
      _ = pullback.fst (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
          diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f ≫ hornRestriction V := by
        rw [hornRestriction_post]
      _ = (fixedFullMap f H ≫ fixedRestriction V (postCoherent f H)) ≫ _ := by
        rw [Category.assoc, restriction_fst]
        simpa only [Category.assoc] using congrArg
          (fun k ↦ k ≫ hornRestriction V) (fixedFullMap_fst f H) |>.symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

#print axioms fixedFullMap_fst
#print axioms fixedHornMap_fst
#print axioms restriction_fst
#print axioms fixedRestriction_post

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedEdgeNaturality
