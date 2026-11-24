import DaggerModelsPartII.JTActualSpanFamilySection
import DaggerModelsPartII.JTOrderedLabelPaddingPrismChainCylinder
import DaggerModelsPartII.JTOrderedLabelPaddingPrismWeakCover
import DaggerModelsPartII.TimePrismChainProjection

/-! The full moving-chain cylinder over the actual finite-support span evaluation. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualSpanPrismChainEvaluation

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTGraphFactoredPresentation (TargetComma)
open JTActualSpanFamilySection (actualFamily actualSpans)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)
variable (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))

private abbrev b := boundaryPoint W x y
private abbrev labels := actualSpans Q A P ⋙ JTGraphSpanLift.spanLabels Q

/-- The chain and prism choices for the actual full-span labels. -/
abbrev Index := JTOrderedLabelPaddingPrismChains.Index W b (labels Q A P)

private abbrev toPrism := JTOrderedLabelPaddingPrismChains.base W b (labels Q A P)

private abbrev toFiniteBase : Index Q A P ⥤ P.FullSubcategory :=
  toPrism Q A P ⋙ JTOrderedLabelPaddingPrismSliceArrow.originalBase W b (labels Q A P)

private abbrev F := actualFamily Q A P
private abbrev reduced := JTOrderedLabelPaddingPrismChainCylinder.reduced (F Q A P)

/-- All internal necklaces of the covered reduced cylinders over the actual spans. -/
abbrev Presentation := BoundaryNecklaceComma.Presentation (reduced Q A P)

private abbrev forget := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced Q A P))

/-- The cover retains the underlying original finite diagram and all its operators. -/
abbrev projection : Presentation Q A P ⥤ P.FullSubcategory :=
  forget Q A P ⋙ toFiniteBase Q A P

/-- Evaluation in the exact original fixed-target comma via the realized labels. -/
abbrev evaluation : Presentation Q A P ⥤ TargetComma Q :=
  JTOrderedLabelPaddingPrismChainCylinder.evaluation (F Q A P)

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The full covered presentation is weak over the original finite diagram. -/
theorem projection_weak (hW : IsFibrant W) :
    WeakEquivalence (nerveMap (projection Q A P)) := by
  letI : WeakEquivalence (nerveMap (forget Q A P)) :=
    JTOrderedLabelPaddingPrismChainCylinder.forget_weak (F Q A P)
  letI : WeakEquivalence (nerveMap (toPrism Q A P)) :=
    TimePrismChainProjection.projection_weak _ _
  letI : WeakEquivalence (nerveMap
    (JTOrderedLabelPaddingPrismSliceArrow.originalBase W b (labels Q A P))) :=
    JTOrderedLabelPaddingPrismWeakCover.originalBase_weak W b (labels Q A P) hW
  change WeakEquivalence (nerveMap (forget Q A P) ≫ nerveMap (toPrism Q A P) ≫
    nerveMap (JTOrderedLabelPaddingPrismSliceArrow.originalBase W b (labels Q A P)))
  infer_instance

end
end DaggerModels.PartII.JTActualSpanPrismChainEvaluation
