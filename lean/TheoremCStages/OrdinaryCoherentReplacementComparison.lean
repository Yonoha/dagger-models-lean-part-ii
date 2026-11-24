import OrdinaryComponentImageDescent
import OrdinaryCoherentArrowVertexRecognition
import OrdinaryCoherentPrecompletionResolution
import OrdinarySegalAllVertexDiagonal
import OrdinaryWalkingPrecompletionExchange
import OriginalSimplicialPiZeroWeakEquivalence

/-!
# The actual coherent-arrow comparison after a rowwise replacement

The vertical diagonal of the original component-saturated coherent-arrow
resolution maps into the literal coherent-arrow image of a chosen replacement.
The map keeps the original arrow row and selected endpoint exactly. Weakness
of this comparison is a separate obligation.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentReplacementComparison

open OrdinaryCSSLocalization (Space walkingSpace)
open OrdinaryCoherentPrecompletionResolution
open OrdinaryCoherentArrowNaturality (walkingMap edgeEvaluation_post)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex coherentEvaluation)

noncomputable section

private abbrev R (W : Space) := OrdinarySegalPrecompletion.resolution W
private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W
private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev vertex : op ⦋1⦌ ⟶ op ⦋0⦌ :=
  (SimplexCategory.const ⦋0⦌ ⦋1⦌ (0 : Fin 2)).op

/-- The literal coherent-arrow inclusion, natural in the whole target. -/
def inclusionNatural : coherentArrowFunctor ⟶
    (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋1⦌) where
  app X := (coherentArrowSubcomplex X).ι
  naturality {_ _} f := OrdinaryCoherentArrowNaturality.coherentArrowMap_inclusion f

/-- The original entire outer coherent-arrow inclusion. -/
def inclusionResolution (W : Space) : coherentResolution W ⟶
    OrdinarySegalResolutionMappingFibers.rowResolution W 1 :=
  Functor.whiskerLeft (R W) inclusionNatural

/-- The inclusion on the literal vertical diagonal targets the actual first row. -/
def diagonalInclusion (W : Space) :
    diagonalFunctor.obj (coherentResolution W) ⟶ (P W).obj (op ⦋1⦌) :=
  diagonalFunctor.map (inclusionResolution W)

/-- The original walking edge evaluation, natural in the whole target. -/
def edgeNatural : diagramMappingTarget walkingSpace ⟶
    (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋1⦌) where
  app X := OrdinarySegalWalkingEvaluation.edgeEvaluation X
  naturality {_ _} f := edgeEvaluation_post f

/-- Evaluate the same directed edge in each original outer row. -/
def edgeResolution (W : Space) :
    OrdinaryWalkingPrecompletionExchange.walkingMappingResolution W ⟶
      OrdinarySegalResolutionMappingFibers.rowResolution W 1 :=
  Functor.whiskerLeft (R W) edgeNatural

/-- Horizontal walking mapping commutes with the actual vertical diagonal. -/
def walkingDiagonalIso (W : Space) :
    OrdinarySegalWalkingEvaluation.walkingMapping (P W) ≅
      diagonalFunctor.obj
        (OrdinaryWalkingPrecompletionExchange.walkingMappingResolution W) :=
  HorizontalMappingVerticalDiagonal.diagramMappingDiagonalIso E (R W) ≪≫
    (diagonalFunctor.mapIso
      (OrdinarySegalAllVertexDiagonal.rowDiscreteMappingIso E (R W))).symm

/-- The diagonal walking edge remains the original edge of the corrected
precompletion, including its horizontal and vertical indices. -/
theorem walkingDiagonal_edge (W : Space) :
    (walkingDiagonalIso W).hom ≫ diagonalFunctor.map (edgeResolution W) =
      OrdinarySegalWalkingEvaluation.edgeEvaluation (P W) := by
  apply NatTrans.ext
  funext q z
  let D := diagonalFunctor.mapIso
    (OrdinarySegalAllVertexDiagonal.rowDiscreteMappingIso E (R W))
  have hD : (walkingDiagonalIso W).hom ≫ D.hom =
      (HorizontalMappingVerticalDiagonal.diagramMappingDiagonalIso E (R W)).hom := by
    simp only [walkingDiagonalIso, D, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hlevel := congrFun (NatTrans.congr_app hD q) z
  change (OrdinaryDiscreteMapping.levelEquiv E ((R W).obj q) q.unop)
      ((walkingDiagonalIso W).hom.app q z) =
    (OrdinaryDiscreteMapping.levelEquiv E (P W) q.unop) z at hlevel
  change (OrdinarySegalWalkingEvaluation.edgeEvaluation ((R W).obj q)).app q
      ((walkingDiagonalIso W).hom.app q z) =
    (OrdinarySegalWalkingEvaluation.edgeEvaluation (P W)).app q z
  rw [OrdinaryCoherentArrowVertexRecognition.edgeEvaluation_level,
    OrdinaryCoherentArrowVertexRecognition.edgeEvaluation_level, hlevel]
  rfl

/-- The whole rowwise evaluation and inclusion recover the directed edge. -/
theorem diagonalEvaluation_inclusion (W : Space) :
    diagonalFunctor.map (evaluationResolution W) ≫ diagonalInclusion W =
      diagonalFunctor.map (edgeResolution W) := by
  have h : evaluationResolution W ≫ inclusionResolution W = edgeResolution W := by
    apply NatTrans.ext
    funext q
    exact OrdinarySegalCoherentArrowImage.coherentEvaluation_inclusion ((R W).obj q)
  rw [diagonalInclusion, ← Functor.map_comp, h]

/-- The selected endpoint of the original coherent resolution is obtained
by restricting the same first-row arrow along its literal vertex zero. -/
theorem diagonalInclusion_endpoint (W : Space) :
    diagonalInclusion W ≫ (P W).map vertex = diagonalEndpoint W := by
  apply NatTrans.ext
  funext q
  rfl

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The exact map into the original replacement arrow row before narrowing
to its coherent component-saturated image. -/
def arrowToReplacement (W T : Space) (j : P W ⟶ T) :
    diagonalFunctor.obj (coherentResolution W) ⟶ T.obj (op ⦋1⦌) :=
  diagonalInclusion W ≫ j.app (op ⦋1⦌)

private theorem arrow_square (W T : Space) (j : P W ⟶ T) :
    diagonalFunctor.map (evaluationResolution W) ≫ arrowToReplacement W T j =
      ((walkingDiagonalIso W).inv ≫ walkingMap j) ≫
        OrdinarySegalWalkingEvaluation.edgeEvaluation T := by
  calc
    diagonalFunctor.map (evaluationResolution W) ≫ arrowToReplacement W T j =
        (diagonalFunctor.map (evaluationResolution W) ≫ diagonalInclusion W) ≫
          j.app (op ⦋1⦌) := by rw [arrowToReplacement, Category.assoc]
    _ = diagonalFunctor.map (edgeResolution W) ≫ j.app (op ⦋1⦌) := by
          rw [diagonalEvaluation_inclusion]
    _ = ((walkingDiagonalIso W).inv ≫
          OrdinarySegalWalkingEvaluation.edgeEvaluation (P W)) ≫
            j.app (op ⦋1⦌) := by
          rw [← walkingDiagonal_edge, ← Category.assoc,
            Iso.inv_hom_id, Category.id_comp]
    _ = ((walkingDiagonalIso W).inv ≫ walkingMap j) ≫
          OrdinarySegalWalkingEvaluation.edgeEvaluation T := by
          rw [Category.assoc, ← edgeEvaluation_post j, ← Category.assoc]

/-- The actual comparison into the coherent-arrow image of the specified
replacement. It is defined by component descent, without claiming weakness. -/
def coherentComparison (W T : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (j : P W ⟶ T) :
    diagonalFunctor.obj (coherentResolution W) ⟶
      (coherentArrowSubcomplex T).toSSet := by
  haveI : WeakEquivalence (diagonalFunctor.map (evaluationResolution W)) :=
    evaluationResolution_diagonal_weak W hSegal
  exact OrdinaryComponentImageDescent.factor
    (diagonalFunctor.map (evaluationResolution W))
    (arrowToReplacement W T j)
    ((walkingDiagonalIso W).inv ≫ walkingMap j)
    (OrdinarySegalWalkingEvaluation.edgeEvaluation T)
    (arrow_square W T j)
    (DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero
      (diagonalFunctor.map (evaluationResolution W))).surjective

/-- The factor keeps the original first-row map of the replacement. -/
theorem coherentComparison_inclusion (W T : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (j : P W ⟶ T) :
    coherentComparison W T hSegal j ≫ (coherentArrowSubcomplex T).ι =
      arrowToReplacement W T j :=
  OrdinaryComponentImageDescent.factor_inclusion _ _ _ _ _ _

/-- The selected endpoint triangle retains the same original vertex zero. -/
theorem coherentComparison_endpoint (W T : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (j : P W ⟶ T) :
    coherentComparison W T hSegal j ≫
        OrdinaryCoherentCompletenessCriterion.endpoint T =
      diagonalEndpoint W ≫ j.app (op ⦋0⦌) := by
  rw [OrdinaryCoherentCompletenessCriterion.endpoint, ← Category.assoc,
    coherentComparison_inclusion, arrowToReplacement, Category.assoc,
    ← j.naturality vertex, ← Category.assoc, diagonalInclusion_endpoint]

#print axioms walkingDiagonal_edge
#print axioms coherentComparison_inclusion
#print axioms coherentComparison_endpoint

end

end DaggerModels.PartII.OrdinaryCoherentReplacementComparison
