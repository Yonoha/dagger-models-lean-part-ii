import OrdinarySegalCotensorParameterNaturality
import OrdinarySegalOrderedMappingFibres
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Public boundary-one mapping calibration

The two original endpoints of a horizontal arrow are the two legs of
mapping out of the literal boundary `∂Δ[1]`. The calibration is natural
in the target simplicial space, so it can be applied to a cotensor
parameter restriction without changing the ordered endpoint convention.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCotensorBoundaryOne

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

private abbrev boundary := (SSet.boundary 1).toSSet
private abbrev boundaryDiagram := discrete.obj boundary

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

/-- Mapping out of the literal horizontal one-boundary is exactly the
ordered product of the two vertex mapping spaces. -/
def boundaryMappingIso (W : Space) :
    diagramMappingSpace boundaryDiagram W ≅
      diagramMappingSpace (discrete.obj (Δ[0] : SSet.{0})) W ⨯
        diagramMappingSpace (discrete.obj (Δ[0] : SSet.{0})) W :=
  IsLimit.conePointUniqueUpToIso (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _))

theorem boundaryMappingIso_fst (W : Space) :
    (boundaryMappingIso W).hom ≫ prod.fst =
      diagramMappingPrecomp boundaryLeg₀ W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.left⟩

theorem boundaryMappingIso_snd (W : Space) :
    (boundaryMappingIso W).hom ≫ prod.snd =
      diagramMappingPrecomp boundaryLeg₁ W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.right⟩

private theorem mapping_pre_post {A B : Space} (i : A ⟶ B)
    {W V : Space} (g : W ⟶ V) :
    diagramMappingPostcomp B g ≫ diagramMappingPrecomp i V =
      diagramMappingPrecomp i W ≫ diagramMappingPostcomp A g := by
  apply NatTrans.ext
  funext q η
  rfl

/-- The literal boundary product comparison is natural in every target map. -/
theorem boundaryMappingIso_natural_target {W V : Space} (g : W ⟶ V) :
    diagramMappingPostcomp boundaryDiagram g ≫ (boundaryMappingIso V).hom =
      (boundaryMappingIso W).hom ≫
        prod.map (diagramMappingPostcomp (discrete.obj (Δ[0] : SSet.{0})) g)
          (diagramMappingPostcomp (discrete.obj (Δ[0] : SSet.{0})) g) := by
  apply prod.hom_ext
  · rw [Category.assoc, boundaryMappingIso_fst,
      Category.assoc, prod.map_fst, ← Category.assoc, boundaryMappingIso_fst]
    exact mapping_pre_post boundaryLeg₀ g
  · rw [Category.assoc, boundaryMappingIso_snd,
      Category.assoc, prod.map_snd, ← Category.assoc, boundaryMappingIso_snd]
    exact mapping_pre_post boundaryLeg₁ g

/-- Identify the same two boundary factors with the original row of
horizontal vertices, preserving the source-target order `(d₁,d₀)`. -/
def endpointTargetIso (W : Space) :
    diagramMappingSpace boundaryDiagram W ≅
      W.obj (op ⦋0⦌) ⨯ W.obj (op ⦋0⦌) :=
  boundaryMappingIso W ≪≫
    prod.mapIso (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0)
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0)

#print axioms boundaryMappingIso
#print axioms boundaryMappingIso_fst
#print axioms boundaryMappingIso_snd
#print axioms boundaryMappingIso_natural_target
#print axioms endpointTargetIso

end
end DaggerModels.PartII.OrdinarySegalCotensorBoundaryOne
