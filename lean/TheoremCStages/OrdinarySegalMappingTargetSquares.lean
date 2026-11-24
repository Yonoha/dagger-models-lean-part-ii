import OrdinarySegalCoherentEdgeNaturality

/-!
# The original horn and edge restrictions commute with target maps

These are exact squares on the original diagram mapping spaces. They
reuse the defined precomposition and postcomposition, without replacing
the horn, its first edge, or the whole target map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalMappingTargetSquares

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentLeftOuterHorn (hornRestriction firstEdgeRestriction)

noncomputable section

/-- Precomposition and target postcomposition give the same whole diagram map. -/
theorem pre_post {A B W V : Space} (i : A ⟶ B) (f : W ⟶ V) :
    diagramMappingPrecomp i W ≫ diagramMappingPostcomp A f =
      diagramMappingPostcomp B f ≫ diagramMappingPrecomp i V := by
  apply NatTrans.ext
  funext n η
  change (Functor.whiskerRight i
    (MonoidalCategory.tensorRight (SSet.stdSimplex.obj n.unop)) ≫ η) ≫ f = _
  exact Category.assoc _ _ _

/-- Naturality at the literal left outer horn. -/
theorem hornRestriction_post {W V : Space} (f : W ⟶ V) :
    hornRestriction W ≫
        diagramMappingPostcomp (discrete.obj (Λ[2, (0 : Fin 3)] : SSet.{0})) f =
      diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f ≫ hornRestriction V :=
  pre_post _ f

/-- Naturality at the same original first edge of the horn. -/
theorem firstEdgeRestriction_post {W V : Space} (f : W ⟶ V) :
    firstEdgeRestriction W ≫ diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f =
      diagramMappingPostcomp (discrete.obj (Λ[2, (0 : Fin 3)] : SSet.{0})) f ≫
        firstEdgeRestriction V :=
  pre_post _ f

/-- The full first-edge restriction retains its original composition. -/
theorem fullFirstEdge_post {W V : Space} (f : W ⟶ V) :
    (hornRestriction W ≫ firstEdgeRestriction W) ≫
        diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f =
      diagramMappingPostcomp (discrete.obj (Δ[2] : SSet.{0})) f ≫
        (hornRestriction V ≫ firstEdgeRestriction V) := by
  rw [Category.assoc, firstEdgeRestriction_post, ← Category.assoc,
    hornRestriction_post, Category.assoc]

#print axioms pre_post
#print axioms hornRestriction_post
#print axioms firstEdgeRestriction_post
#print axioms fullFirstEdge_post

end
end DaggerModels.PartII.OrdinarySegalMappingTargetSquares
