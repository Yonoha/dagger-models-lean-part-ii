import OrdinarySegalMappingTargetSquares
import OrdinarySegalCoherentFixedTriangle

/-!
# Whole target maps on the original fixed-edge triangles and horns

The two actual pullback maps use the original whole coherent edge, its
postcomposition, and the identity of the fixed zero-simplex. Restriction
to the left horn commutes with these maps on the nose.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedEdgeNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentLeftOuterHorn
open OrdinarySegalMappingTargetSquares

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- Postcompose the original whole coherent edge in the actual restriction. -/
def postCoherent {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    E ⟶ diagramRestriction (Δ[0] : SSet.{0}) V.flip :=
  H ≫ diagramRestrictionPost (Δ[0] : SSet.{0})
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f)

/-- The whole first-edge-fixed triangle transforms by original mapping postcomposition. -/
def fixedFullMap {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ⟶
      pullback (hornRestriction V ≫ firstEdgeRestriction V)
        (coherentEdge V (postCoherent f H)) :=
  pullback.map _ _ _ _
    (diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f) (𝟙 _)
    (diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f)
    (fullFirstEdge_post f)
    (by simpa only [Category.id_comp] using
      OrdinarySegalCoherentEdgeNaturality.coherentEdge_post f H)

/-- The same target map transforms the original fixed-first-edge horn. -/
def fixedHornMap {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (firstEdgeRestriction W) (coherentEdge W H) ⟶
      pullback (firstEdgeRestriction V) (coherentEdge V (postCoherent f H)) :=
  pullback.map _ _ _ _
    (diagramMappingPostcomp (discrete.obj (Λ[2, (0 : Fin 3)] : SSet.{0})) f) (𝟙 _)
    (diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f)
    (firstEdgeRestriction_post f)
    (by simpa only [Category.id_comp] using
      OrdinarySegalCoherentEdgeNaturality.coherentEdge_post f H)

theorem fixedFullMap_fst {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedFullMap f H ≫ pullback.fst
        (hornRestriction V ≫ firstEdgeRestriction V) (coherentEdge V (postCoherent f H)) =
      pullback.fst (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f := by
  simp only [fixedFullMap, pullback.map, pullback.lift_fst]

theorem fixedHornMap_fst {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedHornMap f H ≫ pullback.fst
        (firstEdgeRestriction V) (coherentEdge V (postCoherent f H)) =
      pullback.fst (firstEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPostcomp (discrete.obj (Λ[2, (0 : Fin 3)] : SSet.{0})) f := by
  simp only [fixedHornMap, pullback.map, pullback.lift_fst]

theorem restriction_fst (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedRestriction W H ≫ pullback.fst (firstEdgeRestriction W) (coherentEdge W H) =
      pullback.fst (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
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
          pullback.fst (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
            hornRestriction W ≫
              diagramMappingPostcomp (discrete.obj (Λ[2, (0 : Fin 3)] : SSet.{0})) f := by
        rw [Category.assoc, fixedHornMap_fst, ← Category.assoc, restriction_fst,
          Category.assoc]
      _ = pullback.fst (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
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
end DaggerModels.PartII.OrdinarySegalCoherentFixedEdgeNaturality
