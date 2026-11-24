import DaggerModelsPartII.JTActualSpanEndpointPadding
import DaggerModelsPartII.JTInternalTraversalLifts
import DaggerModelsPartII.JTNecklacePrismQuotientWeak

/-! The whole exact prism lifts give a weak cover of every actual finite span. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualSpanPrismLiftCover

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTActualSpanFamilySection (actualSpans)
open JTParametrizedTargetFamilies (codes)
open JTInternalTraversalLifts (TimePresentation sourceFromTime sourceFromTime_weak)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private theorem precompZigzag {B C D : Type} [SmallCategory B] [SmallCategory C] [SmallCategory D]
    (p : B ⥤ C) {F G : C ⥤ D} (h : NatTransZigzag F G) : NatTransZigzag (p ⋙ F) (p ⋙ G) := by
  induction h with
  | rel _ _ h => exact .rel _ _ ⟨Functor.whiskerLeft p h.some⟩
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)
variable (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))

private abbrev N := codes (actualSpans Q A P ⋙ JTGraphSpanLift.spanLabels Q) ⋙
  JTNativeEndpointPadding.pad
private abbrev time := actualSpans Q A P ⋙ JTGraphSpanLift.time Q

/-- At every actual finite span, the positive padded prism gives a weak
comparison on all simplices of the original reduced cylinder diagram. -/
theorem totalQuotient_weak :
    WeakEquivalence (nerveMap (TotalElementsWeakComparison.totalMap
      (Functor.whiskerLeft ((N Q A P).prod' (time Q A P)) JTNecklacePrismQuotientWeak.quotient))) := by
  apply JTNecklacePrismQuotientWeak.total_weak
  intro a
  change 0 < 1 + ((((codes (actualSpans Q A P ⋙ JTGraphSpanLift.spanLabels Q)).obj a).len) + 1)
  omega

/-- Add every simultaneous prism lift of the entire internal necklace. -/
abbrev Lifted := (TimePresentation (N Q A P) (time Q A P))ᵒᵖ

private def toPadded : Lifted Q A P ⥤ JTActualSpanEndpointPadding.Presentation Q A P :=
  sourceFromTime (N Q A P) (time Q A P)

/-- Forget all time lifts and project back to the same original finite subcategory. -/
def projection : Lifted Q A P ⥤ P.FullSubcategory :=
  toPadded Q A P ⋙ JTActualSpanEndpointPadding.projection Q A P

theorem projection_weak : WeakEquivalence (nerveMap (projection Q A P)) := by
  haveI : WeakEquivalence (nerveMap (toPadded Q A P)) := sourceFromTime_weak (N Q A P) (time Q A P)
  haveI := JTActualSpanEndpointPadding.projection_weak Q A P
  change WeakEquivalence (nerveMap (toPadded Q A P) ≫ nerveMap (JTActualSpanEndpointPadding.projection Q A P))
  infer_instance

/-- The covered evaluation keeps every actual decorated object in the original fixed target. -/
def evaluation : Lifted Q A P ⥤ TargetComma Q :=
  toPadded Q A P ⋙ JTActualSpanEndpointPadding.decoratedEvaluation Q A P

private abbrev original :=
  P.ι ⋙ JTSemisimplicialSpanEvaluation.evaluation Q A (JTGraphSpanEvaluation.fullEvaluation Q)

/-- The exact covered evaluation is linked to the original one by the inherited zigzag. -/
theorem original_comparison :
    NatTransZigzag (projection Q A P ⋙ original Q A P) (evaluation Q A P) := by
  let b := toPadded Q A P
  let p := JTActualSpanEndpointPadding.projection Q A P
  let e := original Q A P
  exact .trans _ _ _ (.rel _ _ ⟨(Functor.associator b p e).hom⟩)
    (precompZigzag b (JTActualSpanEndpointPadding.original_comparison_decorated Q A P))

section Criterion

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The contraction criterion may be proved after adjoining all actual full-prism lifts. -/
def FiniteFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A)),
        Finite P.FullSubcategory →
        ∃ (E : Cat.{0, 0}) (F : Lifted Q A P ⥤ E) (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧ NatTransZigzag (evaluation Q A P) (F ⋙ G)

/-- Weakly contractible factors of the original evaluation on the prism-lift
cover imply the unchanged paper Theorem C. -/
theorem theoremC_of_finite_factors (h : FiniteFactors) : TheoremCStatement.statement := by
  apply JTGraphSpanSupportCriterion.theoremC_of_support_nullhomotopies
  intro W hW x y Q A hA
  apply FiniteLastVertexSupport.of_finite_full_weak_cover_factors
  intro P hP
  obtain ⟨E, F, G, hE, hg⟩ := h W hW x y Q A hA P hP
  exact ⟨Cat.of (Lifted Q A P), E, projection Q A P, F, G,
    projection_weak Q A P, hE, .trans _ _ _ (original_comparison Q A P) hg⟩

end Criterion

end
end DaggerModels.PartII.JTActualSpanPrismLiftCover
