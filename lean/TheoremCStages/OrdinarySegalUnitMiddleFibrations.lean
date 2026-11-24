import OrdinarySegalTwoTriangleUnitWeak
import DaggerModelsPartII.DiagramMappingPushout
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# The common middle face of a unit triangle is a Kan fibration

The degree-two left outer horn is the actual pushout of its `d₂` and
`d₁` edges over their common source vertex. Its strict mapping space is
therefore the corresponding pullback. Restriction from the full simplex
is a Kan fibration for every injectively Kan fibrant ordinary space.
The first unit triangle with its `d₂` edge degenerate is a base change of
this exact horn restriction. No Segal or completeness hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalUnitMiddleFibrations

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev mapSpace (K : SSet.{0}) (W : Space) :=
  diagramMappingSpace (discrete.obj K) W
private abbrev d₁ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op
private abbrev d₂ (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (Fin.last 2)).op
private abbrev middle (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op
private abbrev s (W : Space) : row W 0 ⟶ row W 1 :=
  W.map (SimplexCategory.σ (0 : Fin 1)).op

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan
      (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ
      (Type 0) SSet.{0}).obj (SimplicialObject.const (Type 0)))
  infer_instance

private def hornPushout : IsPushout
    (discrete.map (SSet.stdSimplex.δ (1 : Fin 2)))
    (discrete.map (SSet.stdSimplex.δ (1 : Fin 2)))
    (discrete.map SSet.horn₂₀.ι₀₁)
    (discrete.map SSet.horn₂₀.ι₀₂) :=
  SSet.horn₂₀.isPushout.{0}.map discrete

private def hornMappingPullback (W : Space) : IsPullback
    (diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₁) W)
    (diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₂) W)
    (diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (1 : Fin 2))) W)
    (diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (1 : Fin 2))) W) :=
  diagramMappingSpace_isPullback hornPushout W

private def hornMappingIso (W : Space) :
    mapSpace (Λ[2, 0] : SSet.{0}) W ≅
      pullback
        (diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.δ (1 : Fin 2))) W)
        (diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.δ (1 : Fin 2))) W) :=
  (hornMappingPullback W).isoPullback

private def rowHornIso (W : Space) :
    mapSpace (Λ[2, 0] : SSet.{0}) W ≅ pullback (d₁ W) (d₁ W) := by
  let e₀ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 0
  let e₁ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 1
  have h : diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (1 : Fin 2))) W ≫ e₀.hom =
      e₁.hom ≫ d₁ W :=
    OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
      (SimplexCategory.δ (1 : Fin 2))
  let m := pullback.map _ _ (d₁ W) (d₁ W)
    e₁.hom e₁.hom e₀.hom h h
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  exact hornMappingIso W ≪≫ asIso m

private theorem rowHornIso_first (W : Space) :
    (rowHornIso W).hom ≫ pullback.fst (d₁ W) (d₁ W) =
      diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₁) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
  simp only [rowHornIso, Iso.trans_hom, asIso_hom, hornMappingIso,
    pullback.map, pullback.lift_fst, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun h ↦ h ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom)
    (hornMappingPullback W).isoPullback_hom_fst

private theorem rowHornIso_second (W : Space) :
    (rowHornIso W).hom ≫ pullback.snd (d₁ W) (d₁ W) =
      diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₂) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
  simp only [rowHornIso, Iso.trans_hom, asIso_hom, hornMappingIso,
    pullback.map, pullback.lift_snd, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun h ↦ h ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom)
    (hornMappingPullback W).isoPullback_hom_snd

/-- The actual row restriction to the two edges of the left outer horn. -/
def leftHornPair (W : Space) : row W 2 ⟶ pullback (d₁ W) (d₁ W) :=
  (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
    diagramMappingPrecomp (discrete.map
      ((Λ[2, 0] : (Δ[2] : SSet.{0}).Subcomplex).ι)) W ≫
      (rowHornIso W).hom

/-- This restriction is Kan fibrant for an injectively Kan fibrant W. -/
theorem leftHornPair_fibration (W : Space) [IsFibrant W] :
    Fibration (leftHornPair W) := by
  haveI : Mono (discrete.map
      ((Λ[2, 0] : (Δ[2] : SSet.{0}).Subcomplex).ι)) :=
    OrdinaryCSSLocalization.discrete_map_mono _
  haveI : Fibration (diagramMappingPrecomp
      (discrete.map ((Λ[2, 0] :
        (Δ[2] : SSet.{0}).Subcomplex).ι)) W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration
      SimplexCategoryᵒᵖ _ W
  dsimp only [leftHornPair]
  infer_instance

private theorem leftHornPair_first (W : Space) :
    leftHornPair W ≫ pullback.fst (d₁ W) (d₁ W) = d₂ W := by
  dsimp only [leftHornPair]
  simp only [Category.assoc]
  rw [rowHornIso_first]
  rw [← Category.assoc
    (diagramMappingPrecomp (discrete.map
      ((Λ[2, 0] : (Δ[2] : SSet.{0}).Subcomplex).ι)) W)
    (diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₁) W)
    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp, SSet.horn.ι_ι]
  change (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
    diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.map (SimplexCategory.δ (Fin.last 2)))) W ≫
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom = d₂ W
  rw [OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (Fin.last 2))]
  simp only [Iso.inv_hom_id_assoc]

private theorem leftHornPair_second (W : Space) :
    leftHornPair W ≫ pullback.snd (d₁ W) (d₁ W) = middle W := by
  dsimp only [leftHornPair]
  simp only [Category.assoc]
  rw [rowHornIso_second]
  rw [← Category.assoc
    (diagramMappingPrecomp (discrete.map
      ((Λ[2, 0] : (Δ[2] : SSet.{0}).Subcomplex).ι)) W)
    (diagramMappingPrecomp (discrete.map SSet.horn₂₀.ι₀₂) W)
    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp, SSet.horn.ι_ι]
  change (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
    diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)))) W ≫
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom = middle W
  rw [OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (1 : Fin 3))]
  simp only [Iso.inv_hom_id_assoc]

private theorem s_d₁ (W : Space) : s W ≫ d₁ W = 𝟙 (row W 0) := by
  have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1) =
      𝟙 ⦋0⦌ := by
    ext j
    fin_cases j
    rfl
  calc
    s W ≫ d₁ W = W.map
        (SimplexCategory.δ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1)).op := by
            rw [op_comp, Functor.map_comp]
    _ = 𝟙 (row W 0) := by rw [h, op_id, W.map_id]

private theorem shared_vertex (W : Space) :
    d₂ W ≫ d₁ W = middle W ≫ d₁ W := by
  have h : SimplexCategory.δ (1 : Fin 2) ≫
      SimplexCategory.δ (Fin.last 2) =
      SimplexCategory.δ (1 : Fin 2) ≫
        SimplexCategory.δ (1 : Fin 3) := by
    ext j
    fin_cases j
    rfl
  rw [← W.map_comp, ← W.map_comp]
  exact congrArg W.map (congrArg Quiver.Hom.op h)

/-- The first unit square's literal d₁ face, retaining its vertex. -/
def firstCommonFace (W : Space) :
    pullback (d₂ W) (s W) ⟶ row W 1 :=
  pullback.fst (d₂ W) (s W) ≫ middle W

private def unitHornAnchor (W : Space) :
    row W 1 ⟶ pullback (d₁ W) (d₁ W) :=
  pullback.lift (d₁ W ≫ s W) (𝟙 _) (by
    rw [Category.assoc, s_d₁, Category.comp_id, Category.id_comp])

private theorem firstCommon_vertex (W : Space) :
    firstCommonFace W ≫ d₁ W = pullback.snd (d₂ W) (s W) := by
  dsimp only [firstCommonFace]
  rw [Category.assoc, ← shared_vertex W, ← Category.assoc,
    pullback.condition, Category.assoc, s_d₁, Category.comp_id]

/-- The first unit pullback is exactly the base change of the native
left outer-horn restriction along the edge with its degenerate first leg. -/
theorem firstCommon_isPullback (W : Space) :
    IsPullback (pullback.fst (d₂ W) (s W)) (firstCommonFace W)
      (leftHornPair W) (unitHornAnchor W) := by
  haveI : Mono (s W) := mono_of_mono_fac (s_d₁ W)
  haveI : Mono (pullback.fst (d₂ W) (s W)) := inferInstance
  refine {
    w := ?_
    isLimit' := ?_ }
  · apply pullback.hom_ext
    · calc
        (pullback.fst (d₂ W) (s W) ≫ leftHornPair W) ≫
            pullback.fst (d₁ W) (d₁ W) =
          pullback.fst (d₂ W) (s W) ≫ d₂ W := by
            rw [Category.assoc, leftHornPair_first]
        _ = pullback.snd (d₂ W) (s W) ≫ s W := pullback.condition
        _ = (firstCommonFace W ≫ d₁ W) ≫ s W := by
          rw [firstCommon_vertex]
        _ = (firstCommonFace W ≫ unitHornAnchor W) ≫
            pullback.fst (d₁ W) (d₁ W) := by
          simp only [Category.assoc, unitHornAnchor, pullback.lift_fst]
    · calc
        (pullback.fst (d₂ W) (s W) ≫ leftHornPair W) ≫
            pullback.snd (d₁ W) (d₁ W) =
          pullback.fst (d₂ W) (s W) ≫ middle W := by
            rw [Category.assoc, leftHornPair_second]
        _ = firstCommonFace W := rfl
        _ = (firstCommonFace W ≫ unitHornAnchor W) ≫
            pullback.snd (d₁ W) (d₁ W) := by
          simp only [Category.assoc, unitHornAnchor, pullback.lift_snd,
            Category.comp_id]
  · refine ⟨PullbackCone.IsLimit.mk _
      (fun t ↦ pullback.lift t.fst (t.snd ≫ d₁ W) ?_)
      (fun t ↦ by simp only [pullback.lift_fst])
      (fun t ↦ ?_)
      (fun t m hm _ ↦ ?_)⟩
    · have h := congrArg
        (fun a ↦ a ≫ pullback.fst (d₁ W) (d₁ W)) t.condition
      simpa only [Category.assoc, leftHornPair_first,
        unitHornAnchor, pullback.lift_fst] using h
    · dsimp only [firstCommonFace]
      rw [← Category.assoc, pullback.lift_fst]
      have h := congrArg
        (fun a ↦ a ≫ pullback.snd (d₁ W) (d₁ W)) t.condition
      simpa only [Category.assoc, leftHornPair_second,
        unitHornAnchor, pullback.lift_snd, Category.comp_id] using h
    · apply (cancel_mono (pullback.fst (d₂ W) (s W))).mp
      simpa only [pullback.lift_fst] using hm

/-- The common middle-face projection is Kan fibrant, although the
degeneracy itself need not be a weak equivalence. -/
theorem firstCommonFace_fibration (W : Space) [IsFibrant W] :
    Fibration (firstCommonFace W) := by
  have h : fibrations SSet.{0} (firstCommonFace W) :=
    (fibrations SSet.{0}).of_isPullback (firstCommon_isPullback W)
      ((fibration_iff _).mp (leftHornPair_fibration W))
  exact (fibration_iff _).mpr h

#print axioms leftHornPair_fibration
#print axioms firstCommon_isPullback
#print axioms firstCommonFace_fibration

end

end DaggerModels.PartII.OrdinarySegalUnitMiddleFibrations
