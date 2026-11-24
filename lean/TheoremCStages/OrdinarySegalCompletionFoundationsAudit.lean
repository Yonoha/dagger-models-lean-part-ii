import RawOrdinaryJTUnitCSSWeakRouteAudit
import RawOrdinaryJTEndpointCalibration
import OrdinaryJTOrdinaryInputReedy
import OrdinaryJTOrdinaryInputSegal
import OrdinarySegalLocalization
import OrdinarySegalPrecompletion
import OrdinarySegalCoherentArrowImage
import OrdinarySegalUnitPullbackWeak
import OrdinarySegalFaceFibrations
import TheoremCFromOriginalRawOrderedUnit

/-!
Fresh import and exact-map audit of the ordinary Segal completion foundations.
This is not a Comparator Challenge and does not prove the original raw ordered
unit weak. No ordinary completeness premise is imposed on the original input.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCompletionFoundationsAudit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalUnitPullbackWeak

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

example (W : Space) :
    firstUnitComparison W ≫ pullback.fst
        (W.map (SimplexCategory.δ (Fin.last 2)).op)
        (W.map (SimplexCategory.σ (0 : Fin 1)).op) =
      W.map (SimplexCategory.σ (0 : Fin 2)).op := by
  simp only [firstUnitComparison, KanBinaryUnitPullback.unitComparison, pullback.lift_fst]

example (W : Space) :
    firstUnitComparison W ≫ pullback.snd
        (W.map (SimplexCategory.δ (Fin.last 2)).op)
        (W.map (SimplexCategory.σ (0 : Fin 1)).op) =
      W.map (SimplexCategory.δ (1 : Fin 2)).op := by
  simp only [firstUnitComparison, KanBinaryUnitPullback.unitComparison, pullback.lift_snd]

example (W : Space) :
    secondUnitComparison W ≫ pullback.fst
        (W.map (SimplexCategory.δ (0 : Fin 3)).op)
        (W.map (SimplexCategory.σ (0 : Fin 1)).op) =
      W.map (SimplexCategory.σ (1 : Fin 2)).op := by
  simp only [secondUnitComparison, KanBinaryUnitPullback.unitComparison, pullback.lift_fst]

example (W : Space) :
    secondUnitComparison W ≫ pullback.snd
        (W.map (SimplexCategory.δ (0 : Fin 3)).op)
        (W.map (SimplexCategory.σ (0 : Fin 1)).op) =
      W.map (SimplexCategory.δ (0 : Fin 2)).op := by
  simp only [secondUnitComparison, KanBinaryUnitPullback.unitComparison, pullback.lift_snd]

example (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W) :
    @IsFibrant Space _ OrdinarySegalLocalization.model.categoryWithFibrations _
      (RawOrdinaryJTQuillenTranspose.input W) := by
  apply (OrdinarySegalLocalization.isFibrant_iff _).mpr
  exact ⟨OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW,
    OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal⟩

#print axioms OrdinarySegalLocalization.isFibrant_iff
#print axioms OrdinarySegalPrecompletion.unit
#print axioms OrdinarySegalCoherentArrowImage.range_edgeEvaluation
#print axioms OrdinarySegalComponentSubcomplex.restrict_weakEquivalence
#print axioms OrdinarySegalBinaryComparison.binaryComparison_trivialFibration
#print axioms OrdinarySegalFaceFibrations.face_fibration
#print axioms firstUnitComparison_weak
#print axioms secondUnitComparison_weak
#print axioms RawOrdinaryJTUnitCSSWeak.rawTranspose_cssWeak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end

end DaggerModels.PartII.OrdinarySegalCompletionFoundationsAudit
