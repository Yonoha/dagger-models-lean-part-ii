import OrdinarySegalCoherentOuterHornRow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The fixed left horn is the strict source fiber of its composite edge

The isomorphism uses the original first-edge inclusion, the public horn-row
calibration, symmetry, and Mathlib's horizontal pullback-pasting isomorphism.
It retains the exact coherent edge vertex and the actual row source face.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedHornSourceIso

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentLeftOuterHorn (coherentEdge firstEdgeRestriction)
open OrdinarySegalCoherentOuterHornRow (hornRowIso hornRowIso_first)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op

/-- The selected first edge of the left outer horn is its standard
`(0,1)` edge, with no vertex relabeling. -/
theorem firstEdgeInclusion_zero :
    DaggerModels.PartII.RelativeLeftOuterHornGeometry.firstEdgeInclusion.{0} 0 =
      SSet.horn₂₀.ι₀₁ := by
  change SSet.stdSimplex.map
      (DaggerOriginalOrdinaryKanCoreEdgeMembership.pairOperator
        (0 : Fin 2) (1 : Fin 2) _) ≫
      SSet.horn.ι (0 : Fin 3) (Fin.last 2) _ =
    SSet.horn.ι (0 : Fin 3) 2 _
  have h : DaggerOriginalOrdinaryKanCoreEdgeMembership.pairOperator
      (0 : Fin 2) (1 : Fin 2) (by decide) = 𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  rw [h]
  erw [CategoryTheory.Functor.map_id SSet.stdSimplex ⦋1⦌,
    Category.id_comp]
  rfl

/-- The same coherent edge as a literal vertex in the original row-one
Kan complex. -/
def coherentRowEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (Δ[0] : SSet.{0}) ⟶ row W 1 :=
  coherentEdge W H ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom

/-- The fixed coherent left horn is canonically the strict fiber of the
source face at the source vertex of the same original edge. -/
def hornSourceIso (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (firstEdgeRestriction W) (coherentEdge W H) ≅
      pullback (sourceFace W) (coherentRowEdge W H ≫ sourceFace W) := by
  let e₁ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 1
  let r := hornRowIso W
  have hfirst : firstEdgeRestriction W ≫ e₁.hom =
      r.hom ≫ pullback.fst (sourceFace W) (sourceFace W) := by
    rw [firstEdgeRestriction, firstEdgeInclusion_zero]
    exact (hornRowIso_first W).symm
  let m := pullback.map (firstEdgeRestriction W) (coherentEdge W H)
    (pullback.fst (sourceFace W) (sourceFace W)) (coherentRowEdge W H)
    r.hom (𝟙 _) e₁.hom hfirst (by rfl)
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  exact asIso m ≪≫
    pullbackSymmetry (pullback.fst (sourceFace W) (sourceFace W))
      (coherentRowEdge W H) ≪≫
    pullbackRightPullbackFstIso (sourceFace W) (sourceFace W)
      (coherentRowEdge W H) ≪≫
    pullbackSymmetry (coherentRowEdge W H ≫ sourceFace W) (sourceFace W)

#print axioms firstEdgeInclusion_zero
#print axioms hornSourceIso

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedHornSourceIso
