import OrdinarySegalCoherentFixedEdgeNaturality

/-!
# Whole target maps on the literal fixed-edge, fixed-target triangle space

The target vertex is its actual image under the original row-zero map.
The original full two-simplex and its composite edge are retained, and
the maps are defined by the actual two pullback squares.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedTriangleNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentLeftOuterHorn
open OrdinarySegalCoherentOuterHornRow (hornRowIso_second)
open OrdinarySegalCoherentFixedTriangle
open OrdinarySegalCoherentFixedEdgeNaturality
open OrdinarySegalRestrictionTargetNaturality (simplexMappingIso_post)
open OrdinarySegalMappingTargetSquares (pre_post)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

theorem hornComposite_eq (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    hornComposite W H =
      pullback.fst (firstEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₂) W ≫
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
  rw [hornComposite, hornRowIso_second]

/-- The composite edge transforms by the actual degree-one target map. -/
theorem hornComposite_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedHornMap f H ≫ hornComposite V (postCoherent f H) =
      hornComposite W H ≫ f.app (op ⦋1⦌) := by
  calc
    fixedHornMap f H ≫ hornComposite V (postCoherent f H) =
        fixedHornMap f H ≫
          pullback.fst (firstEdgeRestriction V) (coherentEdge V (postCoherent f H)) ≫
            diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₂) V ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso V 1).hom := by
      rw [hornComposite_eq]
    _ = pullback.fst (firstEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPostcomp (discrete.obj (Λ[2, (0 : Fin 3)] : SSet.{0})) f ≫
          diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₂) V ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso V 1).hom := by
      rw [← Category.assoc (fixedHornMap f H), fixedHornMap_fst, Category.assoc]
    _ = pullback.fst (firstEdgeRestriction W) (coherentEdge W H) ≫
        diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₂) W ≫
          diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso V 1).hom := by
      rw [← Category.assoc
        (diagramMappingPostcomp (discrete.obj (Λ[2, (0 : Fin 3)] : SSet.{0})) f),
        ← pre_post, Category.assoc]
    _ = hornComposite W H ≫ f.app (op ⦋1⦌) := by
      rw [simplexMappingIso_post, hornComposite_eq]
      simp only [Category.assoc]

/-- The fixed final vertex transforms by the original degree-zero map. -/
theorem fixedHornTarget_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedHornMap f H ≫ fixedHornTarget V (postCoherent f H) =
      fixedHornTarget W H ≫ f.app (op ⦋0⦌) := by
  change fixedHornMap f H ≫
      (hornComposite V (postCoherent f H) ≫ V.map (SimplexCategory.δ (0 : Fin 2)).op) =
    (hornComposite W H ≫ W.map (SimplexCategory.δ (0 : Fin 2)).op) ≫ f.app (op ⦋0⦌)
  rw [← Category.assoc, hornComposite_post, Category.assoc,
    ← f.naturality (SimplexCategory.δ (0 : Fin 2)).op, ← Category.assoc]

/-- The same whole target map acts on fixed triangles at the literal image vertex. -/
def fixedTriangleMap {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    fixedTriangle W H y ⟶
      fixedTriangle V (postCoherent f H) (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y) :=
  pullback.map _ _ _ _ (fixedFullMap f H) (𝟙 _) (f.app (op ⦋0⦌))
    (by rw [Category.assoc, ← fixedHornTarget_post, ← Category.assoc,
      fixedRestriction_post, Category.assoc])
    (by simp only [Category.id_comp, SSet.yonedaEquiv_symm_comp])

theorem fixedTriangleMap_fst {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    fixedTriangleMap f H y ≫
        pullback.fst
          (fixedRestriction V (postCoherent f H) ≫ fixedHornTarget V (postCoherent f H))
          (SSet.yonedaEquiv.symm (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y)) =
      pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H) (SSet.yonedaEquiv.symm y) ≫
        fixedFullMap f H := by
  simp only [fixedTriangleMap, pullback.map, pullback.lift_fst]

/-- Naturality retains the full original horizontal two-simplex. -/
theorem fullTriangle_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    fixedTriangleMap f H y ≫
        fullTriangle V (postCoherent f H) (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y) =
      fullTriangle W H y ≫ f.app (op ⦋2⦌) := by
  simp only [fullTriangle, Category.assoc]
  rw [← Category.assoc (fixedTriangleMap f H y), fixedTriangleMap_fst,
    Category.assoc, ← Category.assoc (fixedFullMap f H), fixedFullMap_fst,
    Category.assoc, simplexMappingIso_post]

#print axioms hornComposite_eq
#print axioms hornComposite_post
#print axioms fixedHornTarget_post
#print axioms fixedTriangleMap_fst
#print axioms fullTriangle_post

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedTriangleNaturality
