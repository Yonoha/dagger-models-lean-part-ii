import DaggerModelsPartII.JTStableSpanEvaluation
import DaggerModelsPartII.JTOrderedLabelPaddingPrismWeakCover

/-! Use the actual ordered prism cover of each exact normalized finite span. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTStableSpanOrderedPrismCover

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open BoundaryNecklaceComma (fiberDiagram)

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
variable (hP : Finite P.FullSubcategory)

private abbrev eval := JTStableSpanEvaluation.evaluation Q A P hP
private abbrev b := boundaryPoint W x y

/-- Recover the actual decorated labels of the normalized evaluation. -/
abbrev labels : P.FullSubcategory ⥤ OrderedLabelElements.Index W (b (W := W) (x := x) (y := y)) :=
  eval Q A P hP ⋙ JTTargetCommaPullback.toPullback W x y Q ⋙
    Grothendieck.forget (fiberDiagram (JTTargetCommaPullback.diagram W x y Q))

/-- Choose ordered prisms over the labels of this particular finite diagram. -/
abbrev Index := JTOrderedLabelPaddingPrismCover.Index W (b (W := W) (x := x) (y := y))
  (labels Q A P hP)

/-- The original finite subcategory receives the exact original objects and arrows. -/
abbrev base : Index Q A P hP ⥤ P.FullSubcategory :=
  JTOrderedLabelPaddingPrismSliceArrow.originalBase W (b (W := W) (x := x) (y := y))
    (labels Q A P hP)

/-- The covered evaluation has the original fixed target and uses its same exact functor. -/
abbrev evaluation : Index Q A P hP ⥤ TargetComma Q := base Q A P hP ⋙ eval Q A P hP

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- Every original normalized finite span admits the same prescribed ordered prism cover. -/
theorem base_weak (hW : IsFibrant W) :
    WeakEquivalence (nerveMap (base Q A P hP)) :=
  JTOrderedLabelPaddingPrismWeakCover.originalBase_weak W (b (W := W) (x := x) (y := y))
    (labels Q A P hP) hW

/-- The exact factor obligation on the ordered-prism covers of the actual finite spans. -/
def CoveredFiniteFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))
        (hP : Finite P.FullSubcategory),
        ∃ (E : Cat.{0, 0}) (F : Index Q A P hP ⥤ E) (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧ NatTransZigzag (evaluation Q A P hP) (F ⋙ G)

/-- Contracting the covered normalized finite evaluations gives the original Theorem C. -/
theorem theoremC_of_covered_factors (h : CoveredFiniteFactors) : TheoremCStatement.statement := by
  apply JTStableSpanEvaluation.theoremC_of_normalized_weak_cover_factors
  intro W hW x y Q A hA P hP
  obtain ⟨E, F, G, hE, H⟩ := h W hW x y Q A hA P hP
  exact ⟨Cat.of (Index Q A P hP), E, base Q A P hP, F, G,
    base_weak Q A P hP hW.1, hE, H⟩

end

end DaggerModels.PartII.JTStableSpanOrderedPrismCover
