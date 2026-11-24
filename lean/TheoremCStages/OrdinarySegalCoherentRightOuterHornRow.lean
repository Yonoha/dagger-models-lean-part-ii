import OrdinarySegalCoherentRightOuterHorn
import OrdinarySegalUnitMiddleFibrations
import DaggerModelsPartII.DiagramMappingPushout
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Public row calibration for the literal right outer horn

The previously checked unit-middle construction keeps this row isomorphism
private. Here the same public horn pushout and mapping-limit API expose the
two exact row coordinates needed to transport a fixed coherent edge.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentRightOuterHornRow

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentRightOuterHorn (hornRestriction)

noncomputable section

private abbrev mapSpace (K : SSet.{0}) (W : Space) :=
  diagramMappingSpace (discrete.obj K) W
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev d₀ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op
private abbrev outer (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (0 : Fin 3)).op
private abbrev middle (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan
      (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ
      (Type 0) SSet.{0}).obj (SimplicialObject.const (Type 0)))
  infer_instance

private def hornMappingPullback (W : Space) : IsPullback
    (diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₀₂) W)
    (diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₁₂) W)
    (diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (0 : Fin 2))) W)
    (diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (0 : Fin 2))) W) :=
  diagramMappingSpace_isPullback (SSet.horn₂₂.isPushout.{0}.map discrete) W

private def hornMappingIso (W : Space) :
    mapSpace (Λ[2, Fin.last 2] : SSet.{0}) W ≅
      pullback
        (diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.δ (0 : Fin 2))) W)
        (diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.δ (0 : Fin 2))) W) :=
  (hornMappingPullback W).isoPullback

/-- The horn's two original edges are the literal target-sharing row pair. -/
def hornRowIso (W : Space) :
    mapSpace (Λ[2, Fin.last 2] : SSet.{0}) W ≅ pullback (d₀ W) (d₀ W) := by
  let e₀ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 0
  let e₁ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 1
  have h : diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (0 : Fin 2))) W ≫ e₀.hom =
      e₁.hom ≫ d₀ W :=
    OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
      (SimplexCategory.δ (0 : Fin 2))
  let m := pullback.map _ _ (d₀ W) (d₀ W)
    e₁.hom e₁.hom e₀.hom h h
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  exact hornMappingIso W ≪≫ asIso m

/-- The first horn edge is the original middle face after row calibration. -/
theorem hornRowIso_first (W : Space) :
    (hornRowIso W).hom ≫ pullback.fst (d₀ W) (d₀ W) =
      diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₀₂) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
  simp only [hornRowIso, Iso.trans_hom, asIso_hom, hornMappingIso,
    pullback.map, pullback.lift_fst, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun h ↦ h ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom)
    (hornMappingPullback W).isoPullback_hom_fst

/-- The second horn edge is the original outer face after row calibration. -/
theorem hornRowIso_second (W : Space) :
    (hornRowIso W).hom ≫ pullback.snd (d₀ W) (d₀ W) =
      diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₁₂) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
  simp only [hornRowIso, Iso.trans_hom, asIso_hom, hornMappingIso,
    pullback.map, pullback.lift_snd, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun h ↦ h ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom)
    (hornMappingPullback W).isoPullback_hom_snd

/-- The literal row-two to right-horn pair uses the unchanged horn inclusion. -/
def rowRightHorn (W : Space) : row W 2 ⟶ pullback (d₀ W) (d₀ W) :=
  (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
    hornRestriction W ≫ (hornRowIso W).hom

theorem rowRightHorn_first (W : Space) :
    rowRightHorn W ≫ pullback.fst (d₀ W) (d₀ W) = middle W := by
  dsimp only [rowRightHorn]
  simp only [Category.assoc]
  rw [hornRowIso_first]
  rw [← Category.assoc
    (hornRestriction W)
    (diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₀₂) W)
    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom]
  dsimp only [hornRestriction]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp]
  dsimp only [SSet.horn₂₂.ι₀₂]
  erw [SSet.horn.ι_ι]
  change (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
    diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.map
        (SimplexCategory.δ (1 : Fin 3)))) W ≫
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom = middle W
  rw [OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (1 : Fin 3))]
  simp only [Iso.inv_hom_id_assoc]

theorem rowRightHorn_second (W : Space) :
    rowRightHorn W ≫ pullback.snd (d₀ W) (d₀ W) = outer W := by
  dsimp only [rowRightHorn]
  simp only [Category.assoc]
  rw [hornRowIso_second]
  rw [← Category.assoc
    (hornRestriction W)
    (diagramMappingPrecomp (discrete.map SSet.horn₂₂.ι₁₂) W)
    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom]
  dsimp only [hornRestriction]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp]
  dsimp only [SSet.horn₂₂.ι₁₂]
  erw [SSet.horn.ι_ι]
  change (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
    diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.map
        (SimplexCategory.δ (0 : Fin 3)))) W ≫
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom = outer W
  rw [OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (0 : Fin 3))]
  simp only [Iso.inv_hom_id_assoc]

#print axioms hornRowIso
#print axioms hornRowIso_first
#print axioms hornRowIso_second
#print axioms rowRightHorn_first
#print axioms rowRightHorn_second

end
end DaggerModels.PartII.OrdinarySegalCoherentRightOuterHornRow
