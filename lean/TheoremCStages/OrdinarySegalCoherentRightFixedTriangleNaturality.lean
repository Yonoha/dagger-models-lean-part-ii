import OrdinarySegalCoherentRightFixedEdgeNaturality

/-!
# Whole target maps on the literal fixed-last-edge, fixed-source triangle space

The fixed source vertex transforms by its actual original row-zero image.
The original full triangle and its composite edge are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedTriangleNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentRightOuterHorn
open OrdinarySegalCoherentRightOuterHornRow (hornRowIso_first)
open OrdinarySegalCoherentRightFixedTriangle
open OrdinarySegalCoherentRightFixedEdgeNaturality
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)
open OrdinarySegalRestrictionTargetNaturality (simplexMappingIso_post)
open OrdinarySegalMappingTargetSquares (pre_post)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

theorem hornComposite_eq (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    hornComposite W H =
      pullback.fst (lastEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₀₂) W ≫
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
  rw [hornComposite, hornRowIso_first]

/-- The composite edge transforms by the actual degree-one target map. -/
theorem hornComposite_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedHornMap f H ≫ hornComposite V (postCoherent f H) =
      hornComposite W H ≫ f.app (op ⦋1⦌) := by
  calc
    fixedHornMap f H ≫ hornComposite V (postCoherent f H) =
        fixedHornMap f H ≫
          pullback.fst (lastEdgeRestriction V) (coherentEdge V (postCoherent f H)) ≫
            diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₀₂) V ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso V 1).hom := by
      rw [hornComposite_eq]
    _ = pullback.fst (lastEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPostcomp (discrete.obj (Λ[2, Fin.last 2] : SSet.{0})) f ≫
          diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₀₂) V ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso V 1).hom := by
      rw [← Category.assoc (fixedHornMap f H), fixedHornMap_fst, Category.assoc]
    _ = pullback.fst (lastEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₀₂) W ≫
          diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso V 1).hom := by
      rw [← Category.assoc
        (diagramMappingPostcomp (discrete.obj (Λ[2, Fin.last 2] : SSet.{0})) f),
        ← pre_post, Category.assoc]
    _ = hornComposite W H ≫ f.app (op ⦋1⦌) := by
      rw [simplexMappingIso_post, hornComposite_eq]
      simp only [Category.assoc]

/-- The fixed initial vertex transforms by the original degree-zero map. -/
theorem fixedHornSource_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedHornMap f H ≫ fixedHornSource V (postCoherent f H) =
      fixedHornSource W H ≫ f.app (op ⦋0⦌) := by
  change fixedHornMap f H ≫
      (hornComposite V (postCoherent f H) ≫ V.map (SimplexCategory.δ (1 : Fin 2)).op) =
    (hornComposite W H ≫ W.map (SimplexCategory.δ (1 : Fin 2)).op) ≫ f.app (op ⦋0⦌)
  rw [← Category.assoc, hornComposite_post, Category.assoc,
    ← f.naturality (SimplexCategory.δ (1 : Fin 2)).op, ← Category.assoc]

/-- The same whole target map acts on fixed triangles at the literal source-image vertex. -/
def fixedTriangleMap {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    fixedTriangle W H x ⟶
      fixedTriangle V (postCoherent f H) (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x) :=
  pullback.map _ _ _ _ (fixedFullMap f H) (𝟙 _) (f.app (op ⦋0⦌))
    (by rw [Category.assoc, ← fixedHornSource_post, ← Category.assoc,
      fixedRestriction_post, Category.assoc])
    (by simp only [Category.id_comp, SSet.yonedaEquiv_symm_comp])

theorem fixedTriangleMap_fst {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    fixedTriangleMap f H x ≫
        pullback.fst
          (fixedRestriction V (postCoherent f H) ≫ fixedHornSource V (postCoherent f H))
          (SSet.yonedaEquiv.symm (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x)) =
      pullback.fst (fixedRestriction W H ≫ fixedHornSource W H) (SSet.yonedaEquiv.symm x) ≫
        fixedFullMap f H := by
  simp only [fixedTriangleMap, pullback.map, pullback.lift_fst]

/-- Naturality retains the full original horizontal two-simplex. -/
theorem fullTriangle_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    fixedTriangleMap f H x ≫
        fullTriangle V (postCoherent f H) (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x) =
      fullTriangle W H x ≫ f.app (op ⦋2⦌) := by
  simp only [fullTriangle, Category.assoc]
  rw [← Category.assoc (fixedTriangleMap f H x), fixedTriangleMap_fst,
    Category.assoc, ← Category.assoc (fixedFullMap f H), fixedFullMap_fst,
    Category.assoc, simplexMappingIso_post]

#print axioms hornComposite_eq
#print axioms hornComposite_post
#print axioms fixedHornSource_post
#print axioms fixedTriangleMap_fst
#print axioms fullTriangle_post

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedTriangleNaturality
