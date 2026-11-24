import OrdinaryWalkingExtensionRecognition
import OrdinarySegalCoherentArrowImage
import OrdinarySegalHorizontalRestrictions
import NativeQuasicategoryOpposite

/-!
# Recognition of coherent-arrow vertices in the original horizontal row

Injective fibrancy makes coherent evaluation degreewise surjective onto its
actual component image. The original discrete mapping equivalence therefore
identifies its vertices with edges extending through the original walking
parameter. Native quasicategory invertibility supplies the recognition test.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentArrowVertexRecognition

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalWalkingEvaluation (walkingMapping edgeEvaluation)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)
open DaggerOriginalOrdinaryKanCoreEdgeMembership (edgeIsInvertible)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev unit := JTCylinderCEComparison.simplexUnit.app ⦋1⦌
private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

/-- The actual evaluation is the same directed edge under the discrete mapping equivalence. -/
theorem edgeEvaluation_level (W : Space) (q : SimplexCategoryᵒᵖ)
    (t : (walkingMapping W).obj q) :
    (edgeEvaluation W).app q t =
      SSet.yonedaEquiv (unit ≫ (OrdinaryDiscreteMapping.levelEquiv E W q.unop) t) := by
  have h := congrFun
    (NatTrans.congr_app (OrdinaryDiscreteMapping.mappingIso_natural unit W) q) t
  change SSet.yonedaEquiv
      ((OrdinaryDiscreteMapping.levelEquiv (Δ[1] : SSet.{0}) W q.unop)
        ((diagramMappingPrecomp (discrete.map unit) W).app q t)) = _
  change (OrdinaryDiscreteMapping.levelEquiv (Δ[1] : SSet.{0}) W q.unop)
      ((diagramMappingPrecomp (discrete.map unit) W).app q t) =
    unit ≫ (OrdinaryDiscreteMapping.levelEquiv E W q.unop) t at h
  rw [h]

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Membership of the original arrow vertex is exactly a whole original walking extension. -/
theorem mem_coherent_iff_extension (W : Space) [IsFibrant W]
    (e : (W.obj (op ⦋1⦌)).obj zero) :
    e ∈ (coherentArrowSubcomplex W).obj zero ↔
      ∃ H : E ⟶ W.flip.obj zero,
        unit ≫ H = (SSet.yonedaEquiv (X := W.flip.obj zero) (n := ⦋1⦌)).symm e := by
  rw [← OrdinarySegalCoherentArrowImage.range_edgeEvaluation W]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(OrdinaryDiscreteMapping.levelEquiv E W ⦋0⦌) t, ?_⟩
    apply SSet.yonedaEquiv.injective
    rw [← edgeEvaluation_level W zero t, ht, Equiv.apply_symm_apply]
  · rintro ⟨H, hH⟩
    refine ⟨(OrdinaryDiscreteMapping.levelEquiv E W ⦋0⦌).symm H, ?_⟩
    rw [edgeEvaluation_level, Equiv.apply_symm_apply, hH, Equiv.apply_symm_apply]

/-- With a quasicategorical horizontal row, the actual coherent vertices are
exactly the native invertible edges of that same row. -/
theorem mem_coherent_iff_invertible (W : Space) [IsFibrant W]
    [SSet.Quasicategory (W.flip.obj zero)] (e : (W.obj (op ⦋1⦌)).obj zero) :
    e ∈ (coherentArrowSubcomplex W).obj zero ↔
      edgeIsInvertible (W.flip.obj zero) e := by
  rw [mem_coherent_iff_extension]
  simpa only [Equiv.apply_symm_apply] using
    OrdinaryWalkingExtensionRecognition.walking_extension_iff
      (W.flip.obj zero) ((SSet.yonedaEquiv (X := W.flip.obj zero) (n := ⦋1⦌)).symm e)

/-- Every actual horizontal row of an injectively fibrant Segal space is quasicategorical. -/
theorem horizontalRow_quasicategory (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ) :
    SSet.Quasicategory (W.flip.obj (op ⦋n⦌)) := by
  haveI : SSet.Quasicategory (diagramRestriction (Δ[n] : SSet.{0}) W.flip) :=
    OrdinarySegalHorizontalRestrictions.restriction_quasicategory W hSegal _
  exact DaggerNativeQuasicategoryOpposite.quasicategory_of_iso
    (diagramRestrictionSimplexIso W.flip n)

/-- For the original Segal hypotheses, coherent vertices are exactly native
invertible edges, without an additional horizontal-row assumption. -/
theorem segal_mem_coherent_iff_invertible (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (e : (W.obj (op ⦋1⦌)).obj zero) :
    e ∈ (coherentArrowSubcomplex W).obj zero ↔
      edgeIsInvertible (W.flip.obj zero) e := by
  haveI : SSet.Quasicategory (W.flip.obj zero) := horizontalRow_quasicategory W hSegal 0
  exact mem_coherent_iff_invertible W e

#print axioms edgeEvaluation_level
#print axioms mem_coherent_iff_extension
#print axioms mem_coherent_iff_invertible
#print axioms horizontalRow_quasicategory
#print axioms segal_mem_coherent_iff_invertible

end

end DaggerModels.PartII.OrdinaryCoherentArrowVertexRecognition
