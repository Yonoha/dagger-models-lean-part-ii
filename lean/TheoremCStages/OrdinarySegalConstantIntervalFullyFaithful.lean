import OrdinaryIntervalPrismTwoTriangleSquare
import OrdinarySegalTwoTrianglePasting
import OrdinarySegalOrderedMappingMaps
import OrdinarySegalCotensorFibrant

/-!
# The constant interval section on the original ordered mapping fibers

The literal two-triangle comparison is the homotopy-pullback comparison
for the actual constant interval section. Relative Brown base change then
gives a weak equivalence on the exact ordered fibers at the specified
vertices. Ordinary completeness and a desired weak-equivalence premise
are not assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalConstantIntervalFullyFaithful

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalOrderedMappingFibres
open OrdinarySegalOrderedMappingMaps
open OrdinaryIntervalPrismTwoTriangleSquare
open OrdinarySegalTwoTriangleUnitWeak
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev C (W : Space) := cotensor (Δ[1] : SSet.{0}) W
private abbrev sectionMap (W : Space) := constantSection (Δ[1] : SSet.{0}) W

private theorem endpointMap_calibration (W : Space) :
    endpointMap (sectionMap W) ≫ (endpointIso W).hom = degeneratePair W := by
  change prod.map ((sectionMap W).app (op ⦋0⦌)) ((sectionMap W).app (op ⦋0⦌)) ≫
    prod.map (OrdinaryIntervalPrismMappingIso.intervalZeroIso W).hom
      (OrdinaryIntervalPrismMappingIso.intervalZeroIso W).hom = _
  rw [prod.map_map, constantSection_app_zero]
  rfl

/-- The actual comparison to the pullback of the cotensor endpoint arrow. -/
def comparison (W : Space) : W.obj (op ⦋1⦌) ⟶
    pullback (endpointArrow (C W)) (endpointMap (sectionMap W)) :=
  pullback.lift ((sectionMap W).app (op ⦋1⦌)) (endpointArrow W)
    (endpoint_naturality (sectionMap W)).symm

private def comparisonTargetMap (W : Space) :
    pullback (endpointArrow (C W)) (endpointMap (sectionMap W)) ⟶
      pullback (outerPair W) (degeneratePair W) :=
  pullback.map _ _ _ _ (squareIso W).hom (𝟙 _) (endpointIso W).hom
    (squareIso_outerPair W).symm (by
      rw [Category.id_comp]
      exact endpointMap_calibration W)

private theorem comparison_target (W : Space) :
    comparison W ≫ comparisonTargetMap W = twoTriangleUnitComparison W := by
  apply pullback.hom_ext
  · dsimp only [comparisonTargetMap, pullback.map]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
      comparison, pullback.lift_fst, constantSection_squareIso]
    exact (twoTriangleUnitComparison_fst W).symm
  · dsimp only [comparisonTargetMap, pullback.map]
    rw [Category.assoc, pullback.lift_snd, Category.comp_id,
      comparison, pullback.lift_snd]
    exact (twoTriangleUnitComparison_snd W).symm

/-- The original constant section's endpoint square is homotopy cartesian. -/
theorem comparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (comparison W) := by
  have : IsIso (comparisonTargetMap W) := by
    dsimp only [comparisonTargetMap]
    infer_instance
  have : WeakEquivalence (twoTriangleUnitComparison W) :=
    OrdinarySegalTwoTrianglePasting.twoTriangleUnitComparison_weak W hSegal
  exact weakEquivalence_of_postcomp_of_fac (comparison_target W)

/-- The actual interval constant section is fully faithful on the literal
ordered mapping fibers at the original vertices and their actual images. -/
theorem mappingMap_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap (sectionMap W) x y) := by
  have : IsFibrant (C W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  have : Fibration (endpointArrow W) := endpointArrow_fibration W
  have : Fibration (endpointArrow (C W)) := endpointArrow_fibration (C W)
  let p := endpointArrow W
  let q := endpointArrow (C W)
  let g := endpointMap (sectionMap W)
  let k := pullback.snd q g
  let t := pullback.fst q g
  let b := endpointPoint W x y
  let d := endpointPoint (C W)
    (((sectionMap W).app (op ⦋0⦌)).app (op ⦋0⦌) x)
    (((sectionMap W).app (op ⦋0⦌)).app (op ⦋0⦌) y)
  have hb : b ≫ g = d := point_naturality (sectionMap W) x y
  have ha : comparison W ≫ k = p := pullback.lift_snd _ _ _
  have : WeakEquivalence (comparison W) := comparison_weak W hSegal
  have : Fibration k := inferInstance
  let u := mapOver p k (comparison W) ha b
  have : WeakEquivalence u := mapOver_weakEquivalence p k (comparison W) ha b
  have sq : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b) q d := by
    simpa only [k, t, hb] using
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
  let e := sq.isoPullback
  have he : u ≫ e.hom = mappingMap (sectionMap W) x y := by
    apply pullback.hom_ext
    · rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc,
        mapOver_fst, Category.assoc]
      rw [show comparison W ≫ t = (sectionMap W).app (op ⦋1⦌) from
        pullback.lift_fst _ _ _, mappingMap_fst]
    · rw [Category.assoc, sq.isoPullback_hom_snd, mappingMap_snd]
      dsimp only [u, mapOver]
      exact pullback.lift_snd _ _ _
  rw [← he]
  infer_instance

#print axioms comparison_weak
#print axioms mappingMap_weak

end
end DaggerModels.PartII.OrdinarySegalConstantIntervalFullyFaithful
