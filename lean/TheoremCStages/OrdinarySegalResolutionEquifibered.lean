import BisimplicialEquifibered
import OrdinarySegalResolutionMappingFibers
import OrdinaryGroupoidSimplexTransitionEndpointSquare
import OrdinarySegalResolutionRelativeReedy
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Equifibered ordered endpoint resolution

The global endpoint arrow of the original groupoid-simplex cotensor
resolution is equifibered. Evaluation of the chosen product is transported
through its canonical product isomorphism at both parameter degrees, so the
comparison is the checked original endpoint comparison for the unchanged
parameter transition.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalResolutionEquifibered

open OrdinaryCSSLocalization (Space)
open OrdinarySegalResolutionMappingFibers
open OrdinarySegalOrderedMappingFibres (endpointArrow)
open OrdinarySegalOrderedMappingMaps (endpointMap)
open DaggerModels.PartII.BisimplicialEquifibered

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev R (W : Space) := OrdinarySegalPrecompletion.resolution W
private abbrev base (W : Space) :=
  rowResolution W 0 ⨯ rowResolution W 0

/-- The first chosen-product coordinate is evaluation of the global
first product projection. -/
private theorem rowBaseIso_fst (W : Space) (q : SimplexCategoryᵒᵖ) :
    (rowBaseIso W q).hom ≫ prod.fst =
      (prod.fst : base W ⟶ rowResolution W 0).app q := by
  change prodComparison
      ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
        (rowResolution W 0) (rowResolution W 0) ≫ prod.fst = _
  exact prodComparison_fst _ _ _

/-- The second chosen-product coordinate is evaluation of the global
second product projection. -/
private theorem rowBaseIso_snd (W : Space) (q : SimplexCategoryᵒᵖ) :
    (rowBaseIso W q).hom ≫ prod.snd =
      (prod.snd : base W ⟶ rowResolution W 0).app q := by
  change prodComparison
      ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
        (rowResolution W 0) (rowResolution W 0) ≫ prod.snd = _
  exact prodComparison_snd _ _ _

/-- The product isomorphism intertwines the actual outer transition
with the ordered pair of its two degree-zero components. -/
theorem rowBaseIso_naturality (W : Space)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    (base W).map θ ≫ (rowBaseIso W r).hom =
      (rowBaseIso W q).hom ≫ endpointMap ((R W).map θ) := by
  apply prod.hom_ext
  · calc
      ((base W).map θ ≫ (rowBaseIso W r).hom) ≫ prod.fst =
        (base W).map θ ≫
          (prod.fst : base W ⟶ rowResolution W 0).app r := by
            rw [Category.assoc, rowBaseIso_fst]
      _ = (prod.fst : base W ⟶ rowResolution W 0).app q ≫
            (rowResolution W 0).map θ :=
          (prod.fst : base W ⟶ rowResolution W 0).naturality θ
      _ = ((rowBaseIso W q).hom ≫
            endpointMap ((R W).map θ)) ≫ prod.fst := by
          rw [Category.assoc, endpointMap, prod.map_fst,
            ← Category.assoc, rowBaseIso_fst]
          rfl
  · calc
      ((base W).map θ ≫ (rowBaseIso W r).hom) ≫ prod.snd =
        (base W).map θ ≫
          (prod.snd : base W ⟶ rowResolution W 0).app r := by
            rw [Category.assoc, rowBaseIso_snd]
      _ = (prod.snd : base W ⟶ rowResolution W 0).app q ≫
            (rowResolution W 0).map θ :=
          (prod.snd : base W ⟶ rowResolution W 0).naturality θ
      _ = ((rowBaseIso W q).hom ≫
            endpointMap ((R W).map θ)) ≫ prod.snd := by
          rw [Category.assoc, endpointMap, prod.map_snd,
            ← Category.assoc, rowBaseIso_snd]
          rfl

/-- The global transition pullback is the original cotensor transition
pullback after the two chosen-product isomorphisms. -/
def transitionTargetIso (W : Space) {q r : SimplexCategoryᵒᵖ}
    (θ : q ⟶ r) :
    pullback ((endpointResolution W).app r) ((base W).map θ) ≅
      pullback (endpointArrow ((R W).obj r))
        (endpointMap ((R W).map θ)) :=
  asIso (pullback.map
    ((endpointResolution W).app r) ((base W).map θ)
    (endpointArrow ((R W).obj r))
    (endpointMap ((R W).map θ))
    (𝟙 _) (rowBaseIso W q).hom (rowBaseIso W r).hom
    (by simpa only [Category.id_comp] using endpointResolution_app W r)
    (rowBaseIso_naturality W θ))

private theorem transitionTargetIso_fst (W : Space)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    (transitionTargetIso W θ).hom ≫
        pullback.fst (endpointArrow ((R W).obj r))
          (endpointMap ((R W).map θ)) =
      pullback.fst ((endpointResolution W).app r) ((base W).map θ) := by
  dsimp only [transitionTargetIso, asIso_hom, pullback.map]
  rw [pullback.lift_fst, Category.comp_id]

private theorem transitionTargetIso_snd (W : Space)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    (transitionTargetIso W θ).hom ≫
        pullback.snd (endpointArrow ((R W).obj r))
          (endpointMap ((R W).map θ)) =
      pullback.snd ((endpointResolution W).app r) ((base W).map θ) ≫
        (rowBaseIso W q).hom := by
  dsimp only [transitionTargetIso, asIso_hom, pullback.map]
  rw [pullback.lift_snd]

/-- After the canonical target isomorphism, the generic transition
comparison is precisely the original groupoid-simplex endpoint comparison. -/
theorem transitionComparison_targetIso (W : Space)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    transitionComparison (Arrow.mk (endpointResolution W)) θ ≫
        (transitionTargetIso W θ).hom =
      OrdinaryGroupoidSimplexTransitionEndpointSquare.endpointComparison
        θ.unop W := by
  apply pullback.hom_ext
  · calc
      _ = transitionComparison (Arrow.mk (endpointResolution W)) θ ≫
          pullback.fst ((endpointResolution W).app r) ((base W).map θ) := by
        rw [Category.assoc, transitionTargetIso_fst]
      _ = (rowResolution W 1).map θ :=
        transitionComparison_fst (Arrow.mk (endpointResolution W)) θ
      _ = _ := (OrdinarySegalEndpointSquareFiberwiseRecognition.comparison_fst
        (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ.unop W)).symm
  · calc
      _ = (transitionComparison (Arrow.mk (endpointResolution W)) θ ≫
          pullback.snd ((endpointResolution W).app r) ((base W).map θ)) ≫
            (rowBaseIso W q).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ transitionComparison (Arrow.mk (endpointResolution W)) θ ≫ k)
          (transitionTargetIso_snd W θ)
      _ = (endpointResolution W).app q ≫ (rowBaseIso W q).hom :=
        congrArg (fun k ↦ k ≫ (rowBaseIso W q).hom)
          (transitionComparison_snd (Arrow.mk (endpointResolution W)) θ)
      _ = endpointArrow ((R W).obj q) := endpointResolution_app W q
      _ = _ := (OrdinarySegalEndpointSquareFiberwiseRecognition.comparison_snd
        (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ.unop W)).symm

/-- The actual ordered endpoint resolution is equifibered for an
injectively Kan-fibrant ordinary Segal space. -/
theorem endpointResolution_equifibered (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    Equifibered (Arrow.mk (endpointResolution W)) := by
  intro q r θ
  have h : WeakEquivalence
      (OrdinaryGroupoidSimplexTransitionEndpointSquare.endpointComparison
        θ.unop W) :=
    OrdinaryGroupoidSimplexTransitionEndpointSquare.endpointComparison_weak
      θ.unop W hSegal
  haveI : WeakEquivalence ((transitionTargetIso W θ).hom) := inferInstance
  have hc : WeakEquivalence
      (transitionComparison (Arrow.mk (endpointResolution W)) θ ≫
        (transitionTargetIso W θ).hom) := by
    rw [transitionComparison_targetIso]
    exact h
  haveI := hc
  exact weakEquivalence_of_postcomp
    (transitionComparison (Arrow.mk (endpointResolution W)) θ)
    (transitionTargetIso W θ).hom

/-- The actual relative Reedy replacement of this endpoint resolution
retains its equifibered transition comparisons. -/
theorem relativeEndpointResolution_equifibered (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    Equifibered
      (DaggerNativeReedyRelativeReplacement.relativeReplacement.obj
        (Arrow.mk (endpointResolution W))) :=
  relative_replacement_equifibered
    (Arrow.mk (endpointResolution W))
    (OrdinarySegalResolutionRelativeReedy.endpointResolution_row_fibration W)
    (endpointResolution_equifibered W hSegal)

#print axioms rowBaseIso_naturality
#print axioms transitionComparison_targetIso
#print axioms endpointResolution_equifibered
#print axioms relativeEndpointResolution_equifibered

end

end DaggerModels.PartII.OrdinarySegalResolutionEquifibered
