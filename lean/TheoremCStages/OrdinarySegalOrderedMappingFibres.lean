import OrdinarySegalWalkingEvaluation
import DaggerModelsPartII.DiagramMappingLimits
import DaggerModelsPartII.DiagramMappingPrecompFibration
import TopCatModelCategory.ModelCategorySSet
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Literal ordered mapping fibers of an ordinary simplicial space

The two faces of the one-simplex are retained in source–target order
`(d₁,d₀)`. Their joint map, rather than either separate face map, is a Kan
fibration on an injectively Kan-fibrant ordinary simplicial space. The strict
fiber at two specified vertices is therefore a Kan complex. No Segal or
completeness condition is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingFibres

open OrdinaryCSSLocalization

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

/-- The actual source and target faces of the horizontal one-simplex. -/
def endpointArrow (W : Space) : row W 1 ⟶ row W 0 ⨯ row W 0 :=
  prod.lift
    (W.map (SimplexCategory.δ (1 : Fin 2)).op)
    (W.map (SimplexCategory.δ (0 : Fin 2)).op)

theorem endpointArrow_fst (W : Space) :
    endpointArrow W ≫ prod.fst = W.map (SimplexCategory.δ (1 : Fin 2)).op :=
  prod.lift_fst _ _

theorem endpointArrow_snd (W : Space) :
    endpointArrow W ≫ prod.snd = W.map (SimplexCategory.δ (0 : Fin 2)).op :=
  prod.lift_snd _ _

private abbrev boundary := (SSet.boundary 1).toSSet
private abbrev boundaryDiagram := discrete.obj boundary
private def boundaryInclusion : boundaryDiagram ⟶ discrete.obj (Δ[1] : SSet.{0}) :=
  discrete.map (SSet.boundary 1).ι
private def boundaryLeg₀ : discrete.obj (Δ[0] : SSet.{0}) ⟶ boundaryDiagram :=
  discrete.map SSet.boundary₁.ι₀
private def boundaryLeg₁ : discrete.obj (Δ[0] : SSet.{0}) ⟶ boundaryDiagram :=
  discrete.map SSet.boundary₁.ι₁

private instance : PreservesColimitsOfShape (Discrete WalkingPair) discrete := by
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape (Discrete WalkingPair)
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
      (SimplicialObject.const (Type 0)))
  infer_instance

private def boundaryIsColimit :
    IsColimit (BinaryCofan.mk boundaryLeg₀ boundaryLeg₁) := by
  change IsColimit (BinaryCofan.mk
    (discrete.map SSet.boundary₁.ι₀)
    (discrete.map SSet.boundary₁.ι₁))
  exact mapIsColimitOfPreservesOfIsColimit discrete _ _ SSet.boundary₁.isColimit

private def boundaryMappingIsLimit (W : Space) :
    IsLimit (BinaryFan.mk
      (diagramMappingPrecomp boundaryLeg₀ W)
      (diagramMappingPrecomp boundaryLeg₁ W)) := by
  letI : PreservesLimitsOfShape (Discrete WalkingPair)
      (diagramMappingSource W) :=
    diagramMappingSource_preservesLimitsOfShape (Discrete WalkingPair) W
  have h := mapIsLimitOfPreservesOfIsLimit (diagramMappingSource W)
    boundaryLeg₀.op boundaryLeg₁.op (BinaryCofan.IsColimit.op boundaryIsColimit)
  change IsLimit (BinaryFan.mk
    (diagramMappingPrecomp boundaryLeg₀ W)
    (diagramMappingPrecomp boundaryLeg₁ W)) at h
  exact h

private def boundaryMappingIso (W : Space) :
    diagramMappingSpace boundaryDiagram W ≅
      diagramMappingSpace (discrete.obj (Δ[0] : SSet.{0})) W ⨯
        diagramMappingSpace (discrete.obj (Δ[0] : SSet.{0})) W :=
  IsLimit.conePointUniqueUpToIso (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _))

private theorem boundaryMappingIso_fst (W : Space) :
    (boundaryMappingIso W).hom ≫ prod.fst =
      diagramMappingPrecomp boundaryLeg₀ W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.left⟩

private theorem boundaryMappingIso_snd (W : Space) :
    (boundaryMappingIso W).hom ≫ prod.snd =
      diagramMappingPrecomp boundaryLeg₁ W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.right⟩

private theorem boundaryLeg₀_inclusion :
    boundaryLeg₀ ≫ boundaryInclusion =
      discrete.map (SSet.stdSimplex.δ (1 : Fin 2)) := by
  change discrete.map SSet.boundary₁.ι₀ ≫
    discrete.map (SSet.boundary 1).ι = _
  rw [← Functor.map_comp, SSet.boundary₁.ι₀_ι]

private theorem boundaryLeg₁_inclusion :
    boundaryLeg₁ ≫ boundaryInclusion =
      discrete.map (SSet.stdSimplex.δ (0 : Fin 2)) := by
  change discrete.map SSet.boundary₁.ι₁ ≫
    discrete.map (SSet.boundary 1).ι = _
  rw [← Functor.map_comp, SSet.boundary₁.ι₁_ι]

private def endpointTargetIso (W : Space) :
    diagramMappingSpace boundaryDiagram W ≅ row W 0 ⨯ row W 0 :=
  boundaryMappingIso W ≪≫
    prod.mapIso (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0)
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0)

private def endpointArrowIso (W : Space) :
    Arrow.mk (diagramMappingPrecomp boundaryInclusion W) ≅
      Arrow.mk (endpointArrow W) :=
  Arrow.isoMk (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1)
    (endpointTargetIso W) (by
      change (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom ≫
          endpointArrow W =
        diagramMappingPrecomp boundaryInclusion W ≫ (endpointTargetIso W).hom
      apply prod.hom_ext
      · simp only [Category.assoc, endpointArrow, prod.lift_fst,
          endpointTargetIso, Iso.trans_hom, prod.mapIso_hom, prod.map_fst]
        rw [← Category.assoc (boundaryMappingIso W).hom prod.fst
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom,
          boundaryMappingIso_fst]
        rw [← Category.assoc (diagramMappingPrecomp boundaryInclusion W)
          (diagramMappingPrecomp boundaryLeg₀ W)
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom,
          ← diagramMappingPrecomp_comp, boundaryLeg₀_inclusion]
        exact (OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
          (SimplexCategory.δ (1 : Fin 2))).symm
      · simp only [Category.assoc, endpointArrow, prod.lift_snd,
          endpointTargetIso, Iso.trans_hom, prod.mapIso_hom, prod.map_snd]
        rw [← Category.assoc (boundaryMappingIso W).hom prod.snd
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom,
          boundaryMappingIso_snd]
        rw [← Category.assoc (diagramMappingPrecomp boundaryInclusion W)
          (diagramMappingPrecomp boundaryLeg₁ W)
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom,
          ← diagramMappingPrecomp_comp, boundaryLeg₁_inclusion]
        exact (OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
          (SimplexCategory.δ (0 : Fin 2))).symm)

/-- Joint endpoint restriction is a Kan fibration on every injectively
Kan-fibrant ordinary simplicial space. -/
theorem endpointArrow_fibration (W : Space) [IsFibrant W] :
    Fibration (endpointArrow W) := by
  haveI : Mono boundaryInclusion :=
    discrete_map_mono (SSet.boundary 1).ι
  have h : HomotopicalAlgebra.fibrations SSet.{0}
      (diagramMappingPrecomp boundaryInclusion W) :=
    (fibration_iff _).mp
      (InjectiveKanDiagram.diagramMappingPrecomp_isFibration
        SimplexCategoryᵒᵖ boundaryInclusion W)
  exact (fibration_iff _).mpr
    (((HomotopicalAlgebra.fibrations SSet.{0}).arrow_mk_iso_iff
      (endpointArrowIso W)).mp h)

/-- The ordered boundary point specified by literal vertices `x` and `y`. -/
def endpointPoint (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ row W 0 ⨯ row W 0 :=
  prod.lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

theorem endpointPoint_fst (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) :
    endpointPoint W x y ≫ prod.fst = SSet.yonedaEquiv.symm x :=
  prod.lift_fst _ _

theorem endpointPoint_snd (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) :
    endpointPoint W x y ≫ prod.snd = SSet.yonedaEquiv.symm y :=
  prod.lift_snd _ _

/-- The strict ordered mapping fiber at the original two vertices. -/
def mappingFiber (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (endpointArrow W) (endpointPoint W x y)

theorem mappingFiber_isFibrant (W : Space) [IsFibrant W]
    (x y : (row W 0).obj (op ⦋0⦌)) :
    IsFibrant (mappingFiber W x y) := by
  haveI : Fibration (endpointArrow W) := endpointArrow_fibration W
  change IsFibrant (pullback (endpointArrow W) (endpointPoint W x y))
  exact isFibrant_of_fibration (pullback.snd (endpointArrow W) (endpointPoint W x y))

#print axioms endpointArrow_fst
#print axioms endpointArrow_snd
#print axioms endpointArrow_fibration
#print axioms endpointPoint_fst
#print axioms endpointPoint_snd
#print axioms mappingFiber_isFibrant

end

end DaggerModels.PartII.OrdinarySegalOrderedMappingFibres
