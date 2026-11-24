import DaggerModelsPartII.OrderedNecklaceLabelDiagram
import DaggerModelsPartII.JTInjectiveOrderedEndpointFibration
import DaggerModelsPartII.NecklaceCylinderAugmentation

/-! Kan fibrancy of ordered necklace labels at a fixed boundary point. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerModels.PartII.OrderedNecklaceLabelDiagram
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedNecklaceLabelFibrancy

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev NCode := NecklaceCode

private theorem preserves_binary_coproduct :
    PreservesColimitsOfShape (Discrete WalkingPair) F := by
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      DaggerSSet.toPresheaf.{0} :=
    daggerSSetEquivalencePresheaf.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      ((Functor.whiskeringRight ReverseSimplexᵒᵖ (Type 0) SSet.{0}).obj
        (SimplicialObject.const (Type 0))) := inferInstance
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      discreteDagger.{0} := by
    change PreservesColimitsOfShape (Discrete WalkingPair)
      (DaggerSSet.toPresheaf.{0} ⋙
        (Functor.whiskeringRight ReverseSimplexᵒᵖ (Type 0) SSet.{0}).obj
          (SimplicialObject.const (Type 0)))
    infer_instance
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      freeDagger.{0} :=
    freeDaggerAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  change PreservesColimitsOfShape (Discrete WalkingPair)
    (freeDagger.{0} ⋙ discreteDagger.{0})
  infer_instance

private def free_boundary_isColimit :
    IsColimit (BinaryCofan.mk (F.map SSet.boundary₁.ι₀)
      (F.map SSet.boundary₁.ι₁)) := by
  letI : PreservesColimitsOfShape (Discrete WalkingPair) F := preserves_binary_coproduct
  exact mapIsColimitOfPreservesOfIsColimit F _ _ SSet.boundary₁.isColimit

private def boundary_iso : boundary ≅ F.obj (SSet.boundary 1).toSSet :=
  (coprodIsCoprod (F.obj (Δ[0] : SSet.{0}))
    (F.obj (Δ[0] : SSet.{0}))).coconePointUniqueUpToIso free_boundary_isColimit

private theorem boundary_iso_first :
    (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫ boundary_iso.hom =
      F.map SSet.boundary₁.ι₀ := by
  simpa [boundary_iso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod (F.obj (Δ[0] : SSet.{0})) (F.obj (Δ[0] : SSet.{0})))
      free_boundary_isColimit (.mk WalkingPair.left))

private theorem boundary_iso_last :
    (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫ boundary_iso.hom =
      F.map SSet.boundary₁.ι₁ := by
  simpa [boundary_iso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod (F.obj (Δ[0] : SSet.{0})) (F.obj (Δ[0] : SSet.{0})))
      free_boundary_isColimit (.mk WalkingPair.right))

private theorem boundaryNecklace_factor (T : NCode) :
    boundaryNecklace T = boundary_iso.hom ≫
      F.map (JTNecklaceEndpointCylinder.endpointInclusion T) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, boundary_iso_first, ← F.map_comp]
    change coprod.inl ≫ boundaryNecklace T =
      F.map (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last)
    rw [SSet.boundary₁.ι₀_desc]
    simp only [boundaryNecklace, coprod.inl_desc]
  · rw [← Category.assoc, boundary_iso_last, ← F.map_comp]
    change coprod.inr ≫ boundaryNecklace T =
      F.map (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last)
    rw [SSet.boundary₁.ι₁_desc]
    simp only [boundaryNecklace, coprod.inr_desc]

/-- The free ordered boundary of a positive-length necklace is monic. -/
theorem boundaryNecklace_mono_of_pos (T : NCode) (h : 0 < T.len) :
    Mono (boundaryNecklace T) := by
  rw [boundaryNecklace_factor]
  letI : Mono (JTNecklaceEndpointCylinder.endpointInclusion T) :=
    NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos T h
  letI : Mono (F.map (JTNecklaceEndpointCylinder.endpointInclusion T)) :=
    ReversalDiscreteFreeColimits.map_mono _
  infer_instance

/-- Boundary restriction of the full native label mapping space is a Kan fibration. -/
theorem necklaceBoundaryRestriction_fibration (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W) (T : NCode) (h : 0 < T.len) :
    Fibration ((necklaceBoundaryRestriction W).app (op T)) := by
  letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : IsFibrant W := hW
  letI : Mono (boundaryNecklace T) := boundaryNecklace_mono_of_pos T h
  change Fibration (diagramMappingPrecomp (boundaryNecklace T) W)
  exact InjectiveKanDiagram.diagramMappingPrecomp_isFibration
    ReverseSimplexᵒᵖ (boundaryNecklace T) W

/-- At an actual fixed ordered boundary point, positive-length native necklace labels
form a Kan simplicial set. -/
theorem orderedNecklaceLabels_isFibrant (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W)
    (T : NCode) (h : 0 < T.len) :
    IsFibrant ((orderedNecklaceLabels W b).obj (op T)) := by
  haveI : Fibration ((necklaceBoundaryRestriction W).app (op T)) :=
    necklaceBoundaryRestriction_fibration W hW T h
  change IsFibrant (pullback ((necklaceBoundaryRestriction W).app (op T)) b)
  exact isFibrant_of_fibration
    (pullback.snd ((necklaceBoundaryRestriction W).app (op T)) b)

end

end DaggerModels.PartII.JTOrderedNecklaceLabelFibrancy
