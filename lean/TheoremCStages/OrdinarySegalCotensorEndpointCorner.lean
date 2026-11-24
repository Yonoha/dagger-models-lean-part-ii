import OrdinarySegalCotensorBoundaryOne
import OrdinarySegalCotensorRestrictions
import DaggerModelsPartII.ReducedCylinder
import DaggerModelsPartII.DiagramMappingPushout
import SSetSM7

/-!
# The exact relative one-boundary cotensor corner

For a monomorphic horizontal parameter map, the square of restrictions
against the original `∂Δ[1] ⟶ Δ[1]` has a Kan-fibrant comparison arrow.
Its target is the actual pullback of the four strict diagram mapping
spaces. No rowwise-fibration hypothesis or desired corner property is
assumed. The separate boundary-one calibration identifies its two lower
factors with the original ordered source and target vertices.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorEndpointCorner

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan
      (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
      (SimplicialObject.const (Type 0)))
  infer_instance

private abbrev boundary := (SSet.boundary 1).toSSet
private abbrev i := (SSet.boundary 1).ι

/-- The literal pushout-product of the parameter map with the original
one-simplex boundary, using the same tensor square as the reduced cylinder. -/
def square {K L : SSet.{0}} (f : K ⟶ L) : SSet.PushoutTensor f i :=
  ReducedCylinder.tensorSquare f i

/-- The strict mapping-space corner, with the exact boundary and tensor
orientation required for the relative endpoint square. -/
def corner {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    diagramMappingSpace (discrete.obj (L ⊗ (Δ[1] : SSet.{0}))) W ⟶
      pullback
        (diagramMappingPrecomp (discrete.map (f ▷ boundary)) W)
        (diagramMappingPrecomp (discrete.map (K ◁ i)) W) :=
  pullback.lift
    (diagramMappingPrecomp (discrete.map (L ◁ i)) W)
    (diagramMappingPrecomp (discrete.map (f ▷ (Δ[1] : SSet.{0}))) W)
    (by
      rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
        ← discrete.map_comp, ← discrete.map_comp,
        MonoidalCategory.whisker_exchange])

/-- The exact pushout square becomes the strict mapping pullback. -/
def mappingPullback {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    IsPullback
      (diagramMappingPrecomp (discrete.map (square f).inl) W)
      (diagramMappingPrecomp (discrete.map (square f).inr) W)
      (diagramMappingPrecomp (discrete.map (f ▷ boundary)) W)
      (diagramMappingPrecomp (discrete.map (K ◁ i)) W) :=
  diagramMappingSpace_isPullback ((square f).isPushout.map discrete) W

/-- The complete corner is isomorphic to precomposition along the actual
pushout-product inclusion; both pullback projections are retained. -/
def cornerArrowIso {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    Arrow.mk (diagramMappingPrecomp (discrete.map (square f).ι) W) ≅
      Arrow.mk (corner f W) := by
  let h := mappingPullback f W
  refine Arrow.isoMk (Iso.refl _) h.isoPullback ?_
  change corner f W =
    diagramMappingPrecomp (discrete.map (square f).ι) W ≫ h.isoPullback.hom
  apply pullback.hom_ext
  · rw [Category.assoc, h.isoPullback_hom_fst, corner, pullback.lift_fst,
      ← diagramMappingPrecomp_comp, ← discrete.map_comp]
    exact congrArg (fun g ↦ diagramMappingPrecomp (discrete.map g) W)
      (square f).inl_ι.symm
  · rw [Category.assoc, h.isoPullback_hom_snd, corner, pullback.lift_snd,
      ← diagramMappingPrecomp_comp, ← discrete.map_comp]
    exact congrArg (fun g ↦ diagramMappingPrecomp (discrete.map g) W)
      (square f).inr_ι.symm

/-- A monomorphic parameter and the literal one-boundary have a
monomorphic native pushout-product inclusion. -/
theorem square_mono {K L : SSet.{0}} (f : K ⟶ L) [Mono f] :
    Mono (square f).ι := by
  haveI : Mono i := inferInstance
  change Mono (DaggerSSetSM7.pushoutTensor f i).ι
  rw [DaggerSSetSM7.pushoutTensor_ι]
  exact DaggerSSetSM7.pushoutProduct_mono f i

/-- The entire relative endpoint mapping corner is a Kan fibration,
including its pullback target, for every monomorphic parameter map. -/
theorem corner_fibration {K L : SSet.{0}} (f : K ⟶ L) [Mono f]
    (W : Space) [IsFibrant W] : Fibration (corner f W) := by
  haveI : Mono (square f).ι := square_mono f
  haveI : Mono (discrete.map (square f).ι) :=
    OrdinaryCSSLocalization.discrete_map_mono _
  have h : Fibration
      (diagramMappingPrecomp (discrete.map (square f).ι) W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration SimplexCategoryᵒᵖ _ W
  apply (fibration_iff _).mpr
  exact ((fibrations SSet.{0}).arrow_mk_iso_iff
    (cornerArrowIso f W)).mp ((fibration_iff _).mp h)

private theorem simplexMappingIso_natural_target {W V : Space} (g : W ⟶ V)
    (n : ℕ) :
    diagramMappingPostcomp (discrete.obj (Δ[n] : SSet.{0})) g ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso V n).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W n).hom ≫
        g.app (op ⦋n⦌) := by
  apply NatTrans.ext
  funext q η
  rfl

private theorem endpointTargetIso_fst (W : Space) :
    (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom ≫ prod.fst =
      diagramMappingPrecomp (discrete.map SSet.boundary₁.ι₀) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom := by
  simp only [OrdinarySegalCotensorBoundaryOne.endpointTargetIso,
    Iso.trans_hom, Category.assoc, prod.mapIso_hom, prod.map_fst]
  rw [← Category.assoc,
    OrdinarySegalCotensorBoundaryOne.boundaryMappingIso_fst]
  rfl

private theorem endpointTargetIso_snd (W : Space) :
    (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom ≫ prod.snd =
      diagramMappingPrecomp (discrete.map SSet.boundary₁.ι₁) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom := by
  simp only [OrdinarySegalCotensorBoundaryOne.endpointTargetIso,
    Iso.trans_hom, Category.assoc, prod.mapIso_hom, prod.map_snd]
  rw [← Category.assoc,
    OrdinarySegalCotensorBoundaryOne.boundaryMappingIso_snd]
  rfl

private theorem mapping_pre_post {A B : Space} (j : A ⟶ B)
    {W V : Space} (g : W ⟶ V) :
    diagramMappingPostcomp B g ≫ diagramMappingPrecomp j V =
      diagramMappingPrecomp j W ≫ diagramMappingPostcomp A g := by
  apply NatTrans.ext
  funext q η
  rfl

/-- The public boundary-one comparison commutes with every target map,
including the original cotensor parameter restriction. -/
theorem endpointTargetIso_natural_target {W V : Space} (g : W ⟶ V) :
    diagramMappingPostcomp (discrete.obj boundary) g ≫
        (OrdinarySegalCotensorBoundaryOne.endpointTargetIso V).hom =
      (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom ≫
        prod.map (g.app (op ⦋0⦌)) (g.app (op ⦋0⦌)) := by
  apply prod.hom_ext
  · rw [Category.assoc, endpointTargetIso_fst,
      Category.assoc, prod.map_fst]
    rw [← Category.assoc
      (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom prod.fst
      (g.app (op ⦋0⦌)), endpointTargetIso_fst]
    rw [← Category.assoc, mapping_pre_post, Category.assoc,
      simplexMappingIso_natural_target, ← Category.assoc]
  · rw [Category.assoc, endpointTargetIso_snd,
      Category.assoc, prod.map_snd]
    rw [← Category.assoc
      (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom prod.snd
      (g.app (op ⦋0⦌)), endpointTargetIso_snd]
    rw [← Category.assoc, mapping_pre_post, Category.assoc,
      simplexMappingIso_natural_target, ← Category.assoc]

#print axioms square
#print axioms corner
#print axioms mappingPullback
#print axioms cornerArrowIso
#print axioms square_mono
#print axioms corner_fibration
#print axioms endpointTargetIso_natural_target

end
end DaggerModels.PartII.OrdinarySegalCotensorEndpointCorner
