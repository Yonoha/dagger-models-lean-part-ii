import OrdinarySegalRelativeOuterHorn
import OrdinarySegalRestrictionTranspose
import OrdinaryWalkingParameterInvertibleEdge
import NativeSSetFibrationsOverBaseWeakPullbacks
import DaggerModelsPartII.DiagramMappingPrecompFibration

/-!
# Fixed coherent last edges and the right outer horn

The full degree-two simplex is restricted to the literal right outer horn while
its last edge is the image of one fixed whole `E(1)` map. Every vertical
boundary lifting square transposes to the checked relative outer-horn theorem.
The prescribed boundary simplex and the same fixed edge are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentRightOuterHorn

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalRestrictionTranspose (transpose transpose_pre transpose_coeff)
open DaggerOriginalRightOuterHornInclusions (rightOuterLastEdgeInclusion)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev H₂ : SSet.{0} := (Λ[2, Fin.last 2] : SSet.{0})
private abbrev mapSpace (A : SSet.{0}) (W : Space) :=
  diagramMappingSpace (discrete.obj A) W

/-- The original whole two-simplex restricted to the literal right horn. -/
def hornRestriction (W : Space) : mapSpace (Δ[2] : SSet.{0}) W ⟶ mapSpace H₂ W :=
  diagramMappingPrecomp
    (discrete.map (Λ[2, Fin.last 2].ι : H₂ ⟶ (Δ[2] : SSet.{0}))) W

/-- The exact last edge of that horn. -/
def lastEdgeRestriction (W : Space) : mapSpace H₂ W ⟶
    mapSpace (Δ[1] : SSet.{0}) W :=
  diagramMappingPrecomp (discrete.map (rightOuterLastEdgeInclusion 0)) W

/-- A whole coherent walking map gives a literal vertex of the edge mapping
space by restriction along the original simplex-to-groupoid unit. -/
def coherentEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (Δ[0] : SSet.{0}) ⟶ mapSpace (Δ[1] : SSet.{0}) W :=
  (transpose (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}) W).symm
    (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H)

/-- Restricting full triangles and horns to the same coherent last edge. -/
def fixedRestriction (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ⟶
      pullback (lastEdgeRestriction W) (coherentEdge W H) :=
  DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver
    (hornRestriction W ≫ lastEdgeRestriction W)
    (lastEdgeRestriction W) (hornRestriction W) rfl (coherentEdge W H)

private theorem hornRestriction_fibration (W : Space) [IsFibrant W] :
    Fibration (hornRestriction W) := by
  haveI : Mono (discrete.map
      (Λ[2, Fin.last 2].ι : H₂ ⟶ (Δ[2] : SSet.{0}))) :=
    OrdinaryCSSLocalization.discrete_map_mono _
  exact InjectiveKanDiagram.diagramMappingPrecomp_isFibration
    SimplexCategoryᵒᵖ _ W

private theorem fixedRestriction_fibration (W : Space) [IsFibrant W]
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    Fibration (fixedRestriction W H) := by
  haveI : Fibration (hornRestriction W) := hornRestriction_fibration W
  exact (fibration_iff _).mpr
    (MorphismProperty.of_isPullback (P := fibrations SSet.{0})
      (DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_isPullback
        (hornRestriction W ≫ lastEdgeRestriction W)
        (lastEdgeRestriction W) (hornRestriction W) rfl (coherentEdge W H)).flip
      ((fibration_iff _).mp inferInstance))

/-- Every vertical boundary lifts through the exact fixed-edge restriction. -/
theorem fixedRestriction_boundary_lift (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι (fixedRestriction W H) where
  sq_hasLift := by
    intro α β sq
    let v : (SSet.boundary n).toSSet ⟶ (Δ[n] : SSet.{0}) := (SSet.boundary n).ι
    let u : (Δ[n] : SSet.{0}) ⟶ (Δ[0] : SSet.{0}) :=
      SSet.stdSimplex.objZeroIsTerminal.from _
    let αT := α ≫ pullback.fst
      (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H)
    let βH := β ≫ pullback.fst (lastEdgeRestriction W) (coherentEdge W H)
    have hbase : αT ≫ hornRestriction W = v ≫ βH := by
      have hs := congrArg
        (fun t => t ≫ pullback.fst (lastEdgeRestriction W) (coherentEdge W H)) sq.w
      simpa only [αT, βH, v, fixedRestriction, Category.assoc,
        DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst] using hs
    let φ : H₂ ⟶ diagramRestriction (Δ[n] : SSet.{0}) W.flip :=
      transpose (Δ[n] : SSet.{0}) H₂ W βH
    let γ : (Δ[2] : SSet.{0}) ⟶
        diagramRestriction (SSet.boundary n).toSSet W.flip :=
      transpose (SSet.boundary n).toSSet (Δ[2] : SSet.{0}) W αT
    have w : φ ≫ diagramRestrictionPre v W.flip =
        Λ[2, Fin.last 2].ι ≫ γ := by
      calc
        φ ≫ diagramRestrictionPre v W.flip =
            transpose (SSet.boundary n).toSSet H₂ W (v ≫ βH) :=
          (transpose_pre v W βH).symm
        _ = transpose (SSet.boundary n).toSSet H₂ W
            (αT ≫ hornRestriction W) := by rw [hbase]
        _ = Λ[2, Fin.last 2].ι ≫ γ :=
          transpose_coeff Λ[2, Fin.last 2].ι W αT
    have hpoint : β ≫ pullback.snd (lastEdgeRestriction W) (coherentEdge W H) =
        u := SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _
    have hcritical : βH ≫ lastEdgeRestriction W =
        (β ≫ pullback.snd (lastEdgeRestriction W) (coherentEdge W H)) ≫
          coherentEdge W H := by
      dsimp only [βH]
      simpa only [Category.assoc] using
        congrArg (fun t => β ≫ t)
          (pullback.condition (f := lastEdgeRestriction W)
            (g := coherentEdge W H))
    have hlast : rightOuterLastEdgeInclusion 0 ≫ φ =
        JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫
          (H ≫ diagramRestrictionPre u W.flip) := by
      calc
        rightOuterLastEdgeInclusion 0 ≫ φ =
            transpose (Δ[n] : SSet.{0}) (Δ[1] : SSet.{0}) W
              (βH ≫ lastEdgeRestriction W) :=
          (transpose_coeff (rightOuterLastEdgeInclusion 0) W βH).symm
        _ = transpose (Δ[n] : SSet.{0}) (Δ[1] : SSet.{0}) W
              (u ≫ coherentEdge W H) := by
          simpa only [hpoint] using
            congrArg (transpose (Δ[n] : SSet.{0}) (Δ[1] : SSet.{0}) W)
              hcritical
        _ = transpose (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}) W
              (coherentEdge W H) ≫ diagramRestrictionPre u W.flip :=
          transpose_pre u W (coherentEdge W H)
        _ = JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫
              H ≫ diagramRestrictionPre u W.flip := by
          rw [coherentEdge, Equiv.apply_symm_apply]
          simp only [Category.assoc]
        _ = JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫
              (H ≫ diagramRestrictionPre u W.flip) := rfl
    have he : DaggerOriginalOrdinaryKanCoreEdgeMembership.edgeIsInvertible
        (diagramRestriction (Δ[n] : SSet.{0}) W.flip)
        (SSet.yonedaEquiv (rightOuterLastEdgeInclusion 0 ≫ φ)) := by
      rw [hlast]
      exact OrdinaryWalkingParameterInvertibleEdge.simplexUnit_image_invertible _
        (H ≫ diagramRestrictionPre u W.flip)
    obtain ⟨σ, hσ, hσv⟩ :=
      OrdinarySegalRelativeOuterHorn.restriction_right_outer_horn_lift
        W hSegal v 0 φ γ w he
    let t : (Δ[n] : SSet.{0}) ⟶ mapSpace (Δ[2] : SSet.{0}) W :=
      (transpose (Δ[n] : SSet.{0}) (Δ[2] : SSet.{0}) W).symm σ
    have htH : t ≫ hornRestriction W = βH := by
      apply (transpose (Δ[n] : SSet.{0}) H₂ W).injective
      calc
        transpose (Δ[n] : SSet.{0}) H₂ W (t ≫ hornRestriction W) =
            Λ[2, Fin.last 2].ι ≫
              transpose (Δ[n] : SSet.{0}) (Δ[2] : SSet.{0}) W t :=
          transpose_coeff Λ[2, Fin.last 2].ι W t
        _ = Λ[2, Fin.last 2].ι ≫ σ := by
          dsimp only [t]
          rw [Equiv.apply_symm_apply]
        _ = φ := hσ.symm
        _ = transpose (Δ[n] : SSet.{0}) H₂ W βH := rfl
    have htv : v ≫ t = αT := by
      apply (transpose (SSet.boundary n).toSSet (Δ[2] : SSet.{0}) W).injective
      calc
        transpose (SSet.boundary n).toSSet (Δ[2] : SSet.{0}) W (v ≫ t) =
            transpose (Δ[n] : SSet.{0}) (Δ[2] : SSet.{0}) W t ≫
              diagramRestrictionPre v W.flip := transpose_pre v W t
        _ = σ ≫ diagramRestrictionPre v W.flip := by
          dsimp only [t]
          rw [Equiv.apply_symm_apply]
        _ = γ := hσv
        _ = transpose (SSet.boundary n).toSSet (Δ[2] : SSet.{0}) W αT := rfl
    let z : (Δ[n] : SSet.{0}) ⟶
        pullback (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) :=
      pullback.lift t
        (β ≫ pullback.snd (lastEdgeRestriction W) (coherentEdge W H)) (by
          calc
            t ≫ (hornRestriction W ≫ lastEdgeRestriction W) =
                (t ≫ hornRestriction W) ≫ lastEdgeRestriction W :=
              (Category.assoc _ _ _).symm
            _ = βH ≫ lastEdgeRestriction W := by rw [htH]
            _ = (β ≫ pullback.snd (lastEdgeRestriction W)
                (coherentEdge W H)) ≫ coherentEdge W H := hcritical)
    refine CommSq.HasLift.mk' ⟨z, ?_, ?_⟩
    · apply pullback.hom_ext
      · simpa only [z, αT, Category.assoc, pullback.lift_fst] using htv
      · exact SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _
    · apply pullback.hom_ext
      · simpa only [z, βH, fixedRestriction, Category.assoc,
          DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst,
          pullback.lift_fst, pullback.lift_fst_assoc] using htH
      · simp [z, fixedRestriction,
          DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver]

/-- The actual restriction to a right outer horn with one fixed coherent
last edge is a Kan trivial fibration. -/
theorem fixedRestriction_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    trivialFibrations SSet.{0} (fixedRestriction W H) := by
  haveI : Fibration (fixedRestriction W H) := fixedRestriction_fibration W H
  have hI : SSet.modelCategoryQuillen.I.rlp (fixedRestriction W H) := by
    intro A K i hi
    obtain ⟨n⟩ := hi
    exact fixedRestriction_boundary_lift W hSegal H n
  exact (mem_trivialFibrations_iff _).mpr
    ⟨inferInstance, (SSet.modelCategoryQuillen.weakEquivalence_iff_of_fibration
      (fixedRestriction W H)).mp hI⟩

#print axioms fixedRestriction_boundary_lift
#print axioms fixedRestriction_trivialFibration

end
end DaggerModels.PartII.OrdinarySegalCoherentRightOuterHorn
