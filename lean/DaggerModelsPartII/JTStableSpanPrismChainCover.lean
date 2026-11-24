import DaggerModelsPartII.JTStableSpanOrderedPrismCover
import DaggerModelsPartII.JTOrderedLabelPaddingPrismChains
import DaggerModelsPartII.TimePrismChainProjection

/-! The actual normalized finite evaluations on the weak cover by all moving chains. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTStableSpanPrismChainCover

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTStableSpanOrderedPrismCover (labels)

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

private abbrev b := boundaryPoint W x y

/-- The index of all chosen prisms and coefficient-covering chains for the exact finite diagram. -/
abbrev Index := JTOrderedLabelPaddingPrismChains.Index
  W (b (W := W) (x := x) (y := y)) (labels Q A P hP)

/-- Forget the chain without forgetting any original operator. -/
abbrev toPrismCover : Index Q A P hP ⥤ JTStableSpanOrderedPrismCover.Index Q A P hP :=
  JTOrderedLabelPaddingPrismChains.base
    W (b (W := W) (x := x) (y := y)) (labels Q A P hP)

/-- The chain cover projects all the way to the original finite subcategory. -/
abbrev base : Index Q A P hP ⥤ P.FullSubcategory :=
  toPrismCover Q A P hP ⋙ JTStableSpanOrderedPrismCover.base Q A P hP

/-- The evaluation uses the exact normalized map to the unchanged fixed target. -/
abbrev evaluation : Index Q A P hP ⥤ TargetComma Q :=
  base Q A P hP ⋙ JTStableSpanEvaluation.evaluation Q A P hP

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The original finite diagram has the weak nerve type of this entire chain cover. -/
theorem base_weak (hW : IsFibrant W) :
    WeakEquivalence (nerveMap (base Q A P hP)) := by
  letI : WeakEquivalence (nerveMap (toPrismCover Q A P hP)) :=
    TimePrismChainProjection.projection_weak _ _
  letI := JTStableSpanOrderedPrismCover.base_weak Q A P hP hW
  change WeakEquivalence (nerveMap (toPrismCover Q A P hP) ≫
    nerveMap (JTStableSpanOrderedPrismCover.base Q A P hP))
  infer_instance

/-- The remaining comparison on the actual weak chain covers. -/
def CoveredFiniteFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))
        (hP : Finite P.FullSubcategory),
        ∃ (E : Cat.{0, 0}) (F : Index Q A P hP ⥤ E) (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧ NatTransZigzag (evaluation Q A P hP) (F ⋙ G)

/-- A contractible factor over every actual weak chain cover yields the original Theorem C. -/
theorem theoremC_of_covered_factors (h : CoveredFiniteFactors) : TheoremCStatement.statement := by
  apply JTStableSpanEvaluation.theoremC_of_normalized_weak_cover_factors
  intro W hW x y Q A hA P hP
  obtain ⟨E, F, G, hE, H⟩ := h W hW x y Q A hA P hP
  exact ⟨Cat.of (Index Q A P hP), E, base Q A P hP, F, G,
    base_weak Q A P hP hW.1, hE, H⟩

end
end DaggerModels.PartII.JTStableSpanPrismChainCover
