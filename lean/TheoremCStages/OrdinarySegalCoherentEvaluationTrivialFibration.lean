import OrdinarySegalCoherentArrowImage
import OrdinarySegalRestrictionTranspose
import OrdinarySegalHorizontalRestrictions
import OrdinaryWalkingRelativeUnitExtension
import OrdinaryWalkingParameterInvertibleEdge
import NativeBoundaryJoyalMappingWeak

/-!
# Full vertical-boundary lifting for coherent ordinary arrows

The boundary square for the actual coherent evaluation transposes to a
relative walking-isomorphism extension over the horizontal restriction
inner fibration. Degreewise surjectivity provides a whole coherent family
above the prescribed base simplex, making its original directed edge
invertible. The checked relative walking extension then fills the entire
boundary square. Ordinary completeness is not assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentEvaluationTrivialFibration

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentArrowImage
open OrdinarySegalWalkingEvaluation
open OrdinarySegalRestrictionTranspose
open OrdinarySegalHorizontalRestrictions
open OrdinaryWalkingRelativeUnitExtension
open OrdinaryWalkingParameterInvertibleEdge

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev unit := JTCylinderCEComparison.simplexUnit.app ⦋1⦌

private def edgeInput (W : Space) (n : ℕ)
    (b : (Δ[n] : SSet) ⟶ (coherentArrowSubcomplex W : SSet)) :
    (Δ[n] : SSet) ⟶ diagramMappingSpace (discrete.obj (Δ[1] : SSet)) W :=
  b ≫ (coherentArrowSubcomplex W).ι ≫ (simplexMappingIso W 1).inv

private def edgeMap (W : Space) (n : ℕ)
    (b : (Δ[n] : SSet) ⟶ (coherentArrowSubcomplex W : SSet)) :
    (Δ[1] : SSet) ⟶ diagramRestriction (Δ[n] : SSet) W.flip :=
  transpose (Δ[n] : SSet) (Δ[1] : SSet) W (edgeInput W n b)

private def boundaryMap (W : Space) (n : ℕ)
    (a : (SSet.boundary n : SSet) ⟶ walkingMapping W) :
    J ⟶ diagramRestriction (SSet.boundary n : SSet) W.flip :=
  transpose (SSet.boundary n : SSet) J W a

private theorem edgeInput_comp (W : Space) (n : ℕ)
    (b : (Δ[n] : SSet) ⟶ (coherentArrowSubcomplex W : SSet)) :
    edgeInput W n b ≫ (simplexMappingIso W 1).hom =
      b ≫ (coherentArrowSubcomplex W).ι := by
  dsimp only [edgeInput]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The boundary square transposes to the exact original relative
walking-isomorphism extension problem. -/
private theorem transposed_square (W : Space) (n : ℕ)
    (a : (SSet.boundary n : SSet) ⟶ walkingMapping W)
    (b : (Δ[n] : SSet) ⟶ (coherentArrowSubcomplex W : SSet))
    (w : a ≫ coherentEvaluation W = (SSet.boundary n).ι ≫ b) :
    edgeMap W n b ≫
        diagramRestrictionPre (SSet.boundary n).ι W.flip =
      unit ≫ boundaryMap W n a := by
  have hOriginal : (SSet.boundary n).ι ≫
      (b ≫ (coherentArrowSubcomplex W).ι) =
        a ≫ edgeEvaluation W := by
    calc
      (SSet.boundary n).ι ≫ (b ≫ (coherentArrowSubcomplex W).ι) =
          ((SSet.boundary n).ι ≫ b) ≫
            (coherentArrowSubcomplex W).ι :=
        (Category.assoc _ _ _).symm
      _ = (a ≫ coherentEvaluation W) ≫
          (coherentArrowSubcomplex W).ι := by rw [w]
      _ = a ≫ (coherentEvaluation W ≫
          (coherentArrowSubcomplex W).ι) := Category.assoc _ _ _
      _ = a ≫ edgeEvaluation W := by rw [coherentEvaluation_inclusion]
  have hInput : (SSet.boundary n).ι ≫ edgeInput W n b =
      a ≫ diagramMappingPrecomp (discrete.map unit) W := by
    apply (cancel_mono (simplexMappingIso W 1).hom).mp
    calc
      ((SSet.boundary n).ι ≫ edgeInput W n b) ≫
          (simplexMappingIso W 1).hom =
        (SSet.boundary n).ι ≫
          (edgeInput W n b ≫ (simplexMappingIso W 1).hom) :=
        Category.assoc _ _ _
      _ = (SSet.boundary n).ι ≫
          (b ≫ (coherentArrowSubcomplex W).ι) := by rw [edgeInput_comp]
      _ = a ≫ edgeEvaluation W := hOriginal
      _ = (a ≫ diagramMappingPrecomp (discrete.map unit) W) ≫
          (simplexMappingIso W 1).hom := by
        dsimp only [edgeEvaluation]
        rw [Category.assoc]
  calc
    edgeMap W n b ≫ diagramRestrictionPre (SSet.boundary n).ι W.flip =
        transpose (SSet.boundary n : SSet) (Δ[1] : SSet) W
          ((SSet.boundary n).ι ≫ edgeInput W n b) := by
      exact (transpose_pre (SSet.boundary n).ι W (edgeInput W n b)).symm
    _ = transpose (SSet.boundary n : SSet) (Δ[1] : SSet) W
          (a ≫ diagramMappingPrecomp (discrete.map unit) W) := by rw [hInput]
    _ = unit ≫ boundaryMap W n a := transpose_coeff unit W a

/-- The prescribed whole simplex in the coherent component image has an
invertible directed-edge transpose, obtained from a whole coherent lift. -/
private theorem edgeMap_invertible (W : Space) [IsFibrant W] (n : ℕ)
    (b : (Δ[n] : SSet) ⟶ (coherentArrowSubcomplex W : SSet)) :
    edgeIsInvertible (diagramRestriction (Δ[n] : SSet) W.flip)
      (SSet.yonedaEquiv (edgeMap W n b)) := by
  obtain ⟨h, hh⟩ := coherentEvaluation_degree_surjective W n
    (SSet.yonedaEquiv b)
  let t : (Δ[n] : SSet) ⟶ walkingMapping W := SSet.yonedaEquiv.symm h
  have htEval : t ≫ edgeEvaluation W =
      b ≫ (coherentArrowSubcomplex W).ι := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
    change (edgeEvaluation W).app (op ⦋n⦌) h =
      (coherentArrowSubcomplex W).ι.app (op ⦋n⦌)
        (SSet.yonedaEquiv b)
    have hfac := congrFun (NatTrans.congr_app
      (coherentEvaluation_inclusion W) (op ⦋n⦌)) h
    change (coherentArrowSubcomplex W).ι.app (op ⦋n⦌)
        ((coherentEvaluation W).app (op ⦋n⦌) h) =
      (edgeEvaluation W).app (op ⦋n⦌) h at hfac
    exact hfac.symm.trans (congrArg
      ((coherentArrowSubcomplex W).ι.app (op ⦋n⦌)) hh)
  have htInput : t ≫ diagramMappingPrecomp (discrete.map unit) W =
      edgeInput W n b := by
    apply (cancel_mono (simplexMappingIso W 1).hom).mp
    calc
      (t ≫ diagramMappingPrecomp (discrete.map unit) W) ≫
          (simplexMappingIso W 1).hom = t ≫ edgeEvaluation W := by
        dsimp only [edgeEvaluation]
        rw [Category.assoc]
      _ = b ≫ (coherentArrowSubcomplex W).ι := htEval
      _ = edgeInput W n b ≫ (simplexMappingIso W 1).hom :=
        (edgeInput_comp W n b).symm
  let H : J ⟶ diagramRestriction (Δ[n] : SSet) W.flip :=
    transpose (Δ[n] : SSet) J W t
  have hunit : unit ≫ H = edgeMap W n b := by
    change unit ≫ transpose (Δ[n] : SSet) J W t =
      transpose (Δ[n] : SSet) (Δ[1] : SSet) W (edgeInput W n b)
    rw [← transpose_coeff unit W t, htInput]
  rw [← hunit]
  exact simplexUnit_image_invertible _ H

/-- Every literal vertical-boundary square for coherent evaluation has a
filler retaining its exact boundary and coherent-arrow target simplex. -/
theorem coherentEvaluation_boundary_lift (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ)
    (a : (SSet.boundary n : SSet) ⟶ walkingMapping W)
    (b : (Δ[n] : SSet) ⟶ (coherentArrowSubcomplex W : SSet))
    (w : a ≫ coherentEvaluation W = (SSet.boundary n).ι ≫ b) :
    ∃ l : (Δ[n] : SSet) ⟶ walkingMapping W,
      (SSet.boundary n).ι ≫ l = a ∧ l ≫ coherentEvaluation W = b := by
  let p := diagramRestrictionPre (SSet.boundary n).ι W.flip
  haveI : Mono (SSet.boundary n).ι := inferInstance
  have hp : DaggerNativeInnerHornFactorization.innerFibrations p :=
    restriction_innerFibration W hSegal (SSet.boundary n).ι
  have hC : innerHornFillers (diagramRestriction (Δ[n] : SSet) W.flip) :=
    (innerHornFillers_iff_native_quasicategory _).2
      (restriction_quasicategory W hSegal (Δ[n] : SSet))
  have hD : innerHornFillers
      (diagramRestriction (SSet.boundary n : SSet) W.flip) :=
    (innerHornFillers_iff_native_quasicategory _).2
      (restriction_quasicategory W hSegal (SSet.boundary n : SSet))
  obtain ⟨H, hunit, hbase⟩ := edge_extension_over p hp hC hD
    (edgeMap W n b) (boundaryMap W n a)
    (transposed_square W n a b w) (edgeMap_invertible W n b)
  let l : (Δ[n] : SSet) ⟶ walkingMapping W :=
    (transpose (Δ[n] : SSet) J W).symm H
  have hboundary : (SSet.boundary n).ι ≫ l = a := by
    apply (transpose (SSet.boundary n : SSet) J W).injective
    rw [transpose_pre, Equiv.apply_symm_apply]
    exact hbase
  have hinput : l ≫ diagramMappingPrecomp (discrete.map unit) W =
      edgeInput W n b := by
    apply (transpose (Δ[n] : SSet) (Δ[1] : SSet) W).injective
    rw [transpose_coeff, Equiv.apply_symm_apply]
    exact hunit
  have htarget : l ≫ edgeEvaluation W =
      b ≫ (coherentArrowSubcomplex W).ι := by
    calc
      l ≫ edgeEvaluation W =
          (l ≫ diagramMappingPrecomp (discrete.map unit) W) ≫
            (simplexMappingIso W 1).hom := by
        dsimp only [edgeEvaluation]
        rw [Category.assoc]
      _ = edgeInput W n b ≫ (simplexMappingIso W 1).hom := by
        rw [hinput]
      _ = b ≫ (coherentArrowSubcomplex W).ι := edgeInput_comp W n b
  refine ⟨l, hboundary, ?_⟩
  apply (cancel_mono (coherentArrowSubcomplex W).ι).mp
  rw [Category.assoc, coherentEvaluation_inclusion]
  exact htarget

/-- The actual coherent-arrow evaluation lifts every original vertical
boundary; equivalently it is a Kan trivial fibration. -/
theorem coherentEvaluation_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    trivialFibrations SSet.{0} (coherentEvaluation W) := by
  apply (DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_iff_trivialFibration
    (coherentEvaluation W)).mp
  intro n
  constructor
  intro a b sq
  obtain ⟨l, hl, hr⟩ := coherentEvaluation_boundary_lift W hSegal n a b sq.w
  exact CommSq.HasLift.mk' ⟨l, hl, hr⟩

#print axioms coherentEvaluation_boundary_lift
#print axioms coherentEvaluation_trivialFibration

end

end DaggerModels.PartII.OrdinarySegalCoherentEvaluationTrivialFibration
