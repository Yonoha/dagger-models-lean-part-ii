import OrdinarySegalDegeneracyPullback
import DaggerModelsPartII.SpineOuterFacePushout
import DaggerModelsPartII.OuterFaceSpineGeometry
import DaggerModelsPartII.DiagramMappingPushout
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The actual degree-two spine as a strict mapping pullback

The geometric spine is the pushout of its two edge parts over their common
vertex. Ordinary horizontal discretization preserves this pushout, and the
strict diagram mapping space sends it to a pullback. The resulting iso retains
both literal edge restrictions. The edge and overlap parts are separately
identified with the standard one- and zero-simplices.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalSpineTwoPullback

open OrdinaryCSSLocalization SpineOuterFacePushout OuterFaceSpineGeometry

noncomputable section

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
      (SimplicialObject.const (Type 0)))
  infer_instance

private abbrev mid := (middleSpinePart.{0} 0 : SSet.{0})
private abbrev first := (firstSpinePart.{0} 0 : SSet.{0})
private abbrev last := (lastSpinePart.{0} 0 : SSet.{0})
private abbrev whole := (DaggerNativeStandardSpineInner.spine.{0} 2 : SSet.{0})

private def midFirst : mid ⟶ first := SSet.Subcomplex.homOfLE inf_le_left
private def midLast : mid ⟶ last := SSet.Subcomplex.homOfLE inf_le_right
private def firstWhole : first ⟶ whole := SSet.Subcomplex.homOfLE inf_le_left
private def lastWhole : last ⟶ whole := SSet.Subcomplex.homOfLE inf_le_left

/-- The exact ordinary diagram pushout of the two degree-two spine edges. -/
def discreteSpinePushout : IsPushout
    (discrete.map midFirst) (discrete.map midLast)
      (discrete.map firstWhole) (discrete.map lastWhole) := by
  exact (spinePartsPushout.{0} 0).map discrete

/-- On a fixed target, the full degree-two spine mapping space is the
strict pullback of its two edge-part mapping spaces over the shared part. -/
def mappingPartsPullback (W : Space) : IsPullback
    (diagramMappingPrecomp (discrete.map firstWhole) W)
    (diagramMappingPrecomp (discrete.map lastWhole) W)
    (diagramMappingPrecomp (discrete.map midFirst) W)
    (diagramMappingPrecomp (discrete.map midLast) W) :=
  diagramMappingSpace_isPullback discreteSpinePushout W

/-- The strict pullback isomorphism, with no fibrancy or Segal hypothesis. -/
def mappingPartsIso (W : Space) :
    diagramMappingSpace (discrete.obj whole) W ≅
      pullback (diagramMappingPrecomp (discrete.map midFirst) W)
        (diagramMappingPrecomp (discrete.map midLast) W) :=
  (mappingPartsPullback W).isoPullback

theorem mappingPartsIso_first (W : Space) :
    (mappingPartsIso W).hom ≫
        pullback.fst (diagramMappingPrecomp (discrete.map midFirst) W)
          (diagramMappingPrecomp (discrete.map midLast) W) =
      diagramMappingPrecomp (discrete.map firstWhole) W :=
  (mappingPartsPullback W).isoPullback_hom_fst

theorem mappingPartsIso_last (W : Space) :
    (mappingPartsIso W).hom ≫
        pullback.snd (diagramMappingPrecomp (discrete.map midFirst) W)
          (diagramMappingPrecomp (discrete.map midLast) W) =
      diagramMappingPrecomp (discrete.map lastWhole) W :=
  (mappingPartsPullback W).isoPullback_hom_snd

private theorem smallSpine_top (n : ℕ) (hn : n ≤ 1) :
    DaggerNativeStandardSpineInner.spine.{0} n = ⊤ := by
  apply top_unique
  intro q c hc
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      rw [DaggerNativeStandardSpineInner.mem_spine_iff]
      have hr := (SSet.stdSimplex.asOrderHom c (Fin.last d)).isLt
      omega

private def smallSpineIso (n : ℕ) (hn : n ≤ 1) :
    (DaggerNativeStandardSpineInner.spine.{0} n : SSet.{0}) ≅ (Δ[n] : SSet.{0}) :=
  (eqToIso (congrArg SSet.Subcomplex.toSSet (smallSpine_top n hn))).trans
    (SSet.Subcomplex.topIso (Δ[n] : SSet.{0}))

/-- The small-spine isomorphism has exactly the original subcomplex inclusion as its map. -/
theorem smallSpineIso_hom (n : ℕ) (hn : n ≤ 1) :
    (smallSpineIso n hn).hom = (DaggerNativeStandardSpineInner.spine.{0} n).ι := by
  have transport {X : SSet.{0}} {A B : X.Subcomplex} (h : A = B) :
      (eqToIso (congrArg SSet.Subcomplex.toSSet h)).hom ≫ B.ι = A.ι := by
    cases h
    simp
  change (eqToIso (congrArg SSet.Subcomplex.toSSet (smallSpine_top n hn))).hom ≫
      (⊤ : (Δ[n] : SSet.{0}).Subcomplex).ι =
        (DaggerNativeStandardSpineInner.spine.{0} n).ι
  exact transport (smallSpine_top n hn)

/-- The final edge part is the standard degree-one simplex. -/
def firstPartIso : first ≅ (Δ[1] : SSet.{0}) := by
  letI : IsIso (firstSpinePartMap.{0} 0) := firstSpinePartMap_isIso 0
  exact (asIso (firstSpinePartMap 0)).symm ≪≫ smallSpineIso 1 (by decide)

/-- The initial edge part is the standard degree-one simplex. -/
def lastPartIso : last ≅ (Δ[1] : SSet.{0}) := by
  letI : IsIso (lastSpinePartMap.{0} 0) := lastSpinePartMap_isIso 0
  exact (asIso (lastSpinePartMap 0)).symm ≪≫ smallSpineIso 1 (by decide)

/-- The common vertex part is the standard degree-zero simplex. -/
def middlePartIso : mid ≅ (Δ[0] : SSet.{0}) := by
  letI : IsIso (middleSpinePartMap.{0} 0) := middleSpinePartMap_isIso 0
  exact (asIso (middleSpinePartMap 0)).symm ≪≫ smallSpineIso 0 (by decide)

#print axioms discreteSpinePushout
#print axioms mappingPartsIso
#print axioms mappingPartsIso_first
#print axioms mappingPartsIso_last
#print axioms smallSpineIso_hom
#print axioms firstPartIso
#print axioms lastPartIso
#print axioms middlePartIso

end

end DaggerModels.PartII.OrdinarySegalSpineTwoPullback
