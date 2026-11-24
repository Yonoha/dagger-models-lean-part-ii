import DaggerModelsPartII.JTOrderedConeEvaluator
import DaggerModelsPartII.JTSingleCylinderCEIso
import DaggerModelsPartII.DecoratedNecklaceHomBar
import DaggerModelsPartII.ReducedCylinderDirectedContraction

/-! The three literal ordered Hom weight diagrams have weakly contractible values. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedFrameWeights

open JTOrderedFrameHomBar (orderedHom orderedHom_map)

noncomputable section

/-- Weakness of the terminal map is invariant under a specified weak map. -/
theorem point_GW_iff {X Y : SSet.{0}} (f : X ⟶ Y) [WeakEquivalence f] :
    GW (pointMap X) ↔ GW (pointMap Y) := by
  have h : f ≫ pointMap Y = pointMap X := pointIsTerminal.hom_ext _ _
  rw [← h, ← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW]
  exact weakEquivalence_precomp_iff _ _

private abbrev boundary := JTXiEndpointCollapse.boundary
private def firstBoundary : boundary.obj (op ⦋0⦌) := SSet.yonedaEquiv SSet.boundary₁.ι₀
private def lastBoundary : boundary.obj (op ⦋0⦌) := SSet.yonedaEquiv SSet.boundary₁.ι₁
private def intervalUnder : Under boundary := Under.mk JTCylinderFrame.j

private theorem interval_point_GW : GW (pointMap (orderedHom.obj intervalUnder)) := by
  open DaggerActualRigidificationDirectedIntervalObjects in
  have h : Nonempty (((endpoint.{0} 0) ⟶[SSet.{0}] endpoint.{0} 1).obj (op ⦋0⦌)) := ⟨edge⟩
  apply DaggerActualIteratedGadgetNecklaceComparison.point_GW_of_toUnit
  have ha : BoundaryNecklaceComma.first intervalUnder = SSet.stdSimplex.obj₀Equiv.symm 0 := by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι) = _
    rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
    rfl
  have hb : BoundaryNecklaceComma.last intervalUnder = SSet.stdSimplex.obj₀Equiv.symm 1 := by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι) = _
    rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
    rfl
  change GW (toUnit ((vertexEquiv _ (BoundaryNecklaceComma.first intervalUnder)) ⟶[SSet.{0}]
    vertexEquiv _ (BoundaryNecklaceComma.last intervalUnder)))
  rw [ha, hb]
  exact DaggerActualRigidificationSimplexHomContractibility.simplex_hom_toUnit_GW 1 _ _ h

private theorem prism_time_one (n : ℕ) :
    timeSlice (Δ[n] : SSet.{0}) 1 ≫ simplexPrism n 0 =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply SSet.stdSimplex.ext
    intro i
    change (simplexPrism n 0).app (op ⦋d⦌)
      (x, SSet.stdSimplex.const 1 1 (op ⦋d⦌)) i = Fin.last n
    rw [simplexPrism_app]
    apply Fin.ext
    change max (x i).val (n * 1) = n
    simpa only [Nat.mul_one] using (max_eq_right (Nat.le_of_lt_succ (x i).isLt))

private def standardAugmentation (k : SimplexCategory) :
    JTCylinderFrame.under.obj k ⟶ intervalUnder :=
  Under.homMk (ReducedCylinderDirectedContraction.augmentation
    (K := SSet.stdSimplex.obj k) JTCylinderFrame.j)
    (ReducedCylinderDirectedContraction.boundary_augmentation JTCylinderFrame.j)

private theorem standardAugmentation_weak (k : SimplexCategory) :
    WeakEquivalence (orderedHom.map (standardAugmentation k)) := by
  induction k using SimplexCategory.rec with | _ n =>
    rw [orderedHom_map]
    apply (DaggerActualRigHomWeakCoreRigidification.castMap_weak_iff _ _ _ _ _ _ _).mpr
    have h := ReducedCylinderDirectedContraction.augmentation_endpointHom_weak
      JTCylinderFrame.j _ (simplexPrism n 0) (simplexPrism_time_zero n 0)
      (prism_time_one n) firstBoundary lastBoundary
    simpa only [standardAugmentation, BoundaryNecklaceComma.first_eq,
      BoundaryNecklaceComma.last_eq] using h

/-- Every original standard reduced-cylinder Hom weight contracts at the ordered pair. -/
theorem standard_point_GW (k : SimplexCategory) :
    GW (pointMap ((JTCylinderFrame.under ⋙ orderedHom).obj k)) := by
  letI := standardAugmentation_weak k
  exact (point_GW_iff (orderedHom.map (standardAugmentation k))).mpr interval_point_GW

open DaggerChosenRigidificationNecklace.NecklaceCode in
private theorem single_point_GW (k : SimplexCategory) :
    GW (pointMap ((JTNecklaceEndpointCylinder.under (single 1) ⋙ orderedHom).obj k)) := by
  have h : orderedHom.obj ((JTNecklaceEndpointCylinder.under (single 1)).obj k) =
      NecklaceCylinderHomSpan.cylinderHom (single 1) k := by
    change (vertexEquiv _ (BoundaryNecklaceComma.first _) ⟶[SSet.{0}]
      vertexEquiv _ (BoundaryNecklaceComma.last _)) = _
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    rfl
  change GW (pointMap (orderedHom.obj ((JTNecklaceEndpointCylinder.under (single 1)).obj k)))
  rw [h]
  letI := NecklaceCylinderHomSpan.leftMap_weak (single 1) k
  exact (point_GW_iff (NecklaceCylinderHomSpan.leftMap (single 1) k)).mpr
    (DecoratedNecklaceHomBar.necklaceHom_point_GW (single 1))

/-- Every actual CE Hom weight contracts, using the original one-edge cylinder. -/
theorem ce_point_GW (k : SimplexCategory) :
    GW (pointMap (((Under.lift JTXiEndpointCollapse.CE JTXiEndpointCollapse.CE_boundary) ⋙
      orderedHom).obj k)) :=
  (point_GW_iff (orderedHom.map (JTSingleCylinderCEIso.comparison.hom.app k))).mp
    (single_point_GW k)

/-- The original right-cone Hom weights are the original contractible Q weights. -/
theorem cone_point_GW (k : SimplexCategory) :
    GW (pointMap ((JTCylinderConeComparison.coneUnder ⋙ orderedHom).obj k)) :=
  (point_GW_iff (JTOrderedConeEvaluator.coefficientIso k).hom).mpr
    (DaggerActualIteratedGadgetNecklaceComparison.point_GW_of_toUnit
      (DaggerActualCounitRightConeQHomotopicalDiagram.object_toUnit_GW k))

end

end DaggerModels.PartII.JTOrderedFrameWeights
