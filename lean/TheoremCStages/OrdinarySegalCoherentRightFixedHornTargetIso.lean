import OrdinarySegalCoherentRightOuterHornRow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The fixed right horn is the strict target fiber of its free edge

The literal last-edge inclusion of the right outer horn is calibrated to
the standard `(1,2)` edge. The checked right-horn row isomorphism and
Mathlib's vertical pullback-pasting isomorphism then identify the fixed
horn with the target fiber of the remaining `(0,2)` edge. The entire
coherent edge vertex and its original target face are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedHornTargetIso

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentRightOuterHorn (coherentEdge lastEdgeRestriction)
open OrdinarySegalCoherentRightOuterHornRow (hornRowIso hornRowIso_second)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

/-- The selected last edge of the literal right outer horn is its
standard `(1,2)` edge, with no vertex relabeling. -/
theorem lastEdgeInclusion_zero :
    DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion.{0} 0 =
      SSet.horn₂₂.ι₁₂ := by
  apply (cancel_mono (Λ[2, Fin.last 2]).ι).mp
  rw [DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion_comp]
  dsimp only [SSet.horn₂₂.ι₁₂]
  erw [SSet.horn.ι_ι]
  have h : AugmentedSimplexCategory.inr' ⦋0⦌ ⦋1⦌ =
      SimplexCategory.δ (0 : Fin 3) := by decide
  rw [h]
  rfl

/-- The same coherent last edge as a literal vertex in the original
row-one Kan complex. -/
def coherentRowEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (Δ[0] : SSet.{0}) ⟶ row W 1 :=
  coherentEdge W H ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom

/-- The fixed coherent right horn is canonically the strict fiber of the
target face at the target vertex of the same original last edge. -/
def hornTargetIso (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (lastEdgeRestriction W) (coherentEdge W H) ≅
      pullback (targetFace W) (coherentRowEdge W H ≫ targetFace W) := by
  let e₁ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 1
  let r := hornRowIso W
  have hlast : lastEdgeRestriction W ≫ e₁.hom =
      r.hom ≫ pullback.snd (targetFace W) (targetFace W) := by
    rw [lastEdgeRestriction, lastEdgeInclusion_zero]
    exact (hornRowIso_second W).symm
  let m := pullback.map (lastEdgeRestriction W) (coherentEdge W H)
    (pullback.snd (targetFace W) (targetFace W)) (coherentRowEdge W H)
    r.hom (𝟙 _) e₁.hom hlast (by rfl)
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  exact asIso m ≪≫
    pullbackLeftPullbackSndIso (targetFace W) (targetFace W)
      (coherentRowEdge W H)

#print axioms lastEdgeInclusion_zero
#print axioms hornTargetIso

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedHornTargetIso
