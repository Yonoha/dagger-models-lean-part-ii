import DaggerModelsPartII.JTStablePairedNecklaceDiagram
import DaggerModelsPartII.JTGraphSpanSupportCriterion

/-!
# Normalize each finite support of the exact injective-phase span evaluation

The finite-support factors of the original and simultaneously normalized
diagrams are equivalent conditions, with the original fixed-target comma.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTStableSpanEvaluation

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)

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

private abbrev original :=
  P.ι ⋙ JTSemisimplicialSpanEvaluation.evaluation Q A (JTGraphSpanEvaluation.fullEvaluation Q)

private theorem finite_ends (hP : Finite P.FullSubcategory) (p : P.FullSubcategory) :
    Finite (JTStableEndpointQuotient.Ends p) := by
  letI := hP
  letI (q : P.FullSubcategory) : Finite (p ⟶ q) := by
    letI : Finite (P.ι.obj p ⟶ P.ι.obj q) :=
      JTSemisimplicialSpanEvaluation.resolution_finite_hom Q A p.obj q.obj
    exact Finite.of_injective (fun f : p ⟶ q ↦ P.ι.map f)
      (fun _ _ h ↦ P.ι.map_injective h)
  infer_instance

/-- Normalize the exact span evaluation on the original finite full subcategory. -/
def evaluation (hP : Finite P.FullSubcategory) : P.FullSubcategory ⥤ TargetComma Q :=
  letI := finite_ends Q A P hP
  JTStablePairedNecklaceDiagram.normalizedEvaluation W x y Q (original Q A P)

/-- The entire normalized finite span evaluation compares to the original one. -/
def comparison (hP : Finite P.FullSubcategory) : original Q A P ⟶ evaluation Q A P hP :=
  letI := finite_ends Q A P hP
  JTStablePairedNecklaceDiagram.evaluationComparison W x y Q (original Q A P)

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- Factor the simultaneously normalized evaluations through weakly contractible nerves. -/
def NormalizedFiniteFullFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))
        (hP : Finite P.FullSubcategory),
        ∃ (E : Cat.{0, 0}) (F : P.FullSubcategory ⥤ E) (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧ NatTransZigzag (evaluation Q A P hP) (F ⋙ G)

/-- Simultaneous normalization leaves the exact finite factor obligation equivalent. -/
theorem normalized_factors_iff :
    NormalizedFiniteFullFactors ↔ JTGraphSpanSupportCriterion.FiniteFullFactors := by
  constructor
  · intro h W hW x y Q A hA P hP
    obtain ⟨E, F, G, hE, H⟩ := h W hW x y Q A hA P hP
    exact ⟨E, F, G, hE, .trans _ _ _ (.rel _ _ ⟨comparison Q A P hP⟩) H⟩
  · intro h W hW x y Q A hA P hP
    obtain ⟨E, F, G, hE, H⟩ := h W hW x y Q A hA P hP
    exact ⟨E, F, G, hE, .trans _ _ _ (.symm _ _ (.rel _ _ ⟨comparison Q A P hP⟩)) H⟩

/-- Contracting the normalized finite span evaluations proves the original Theorem C. -/
theorem theoremC_of_normalized_factors (h : NormalizedFiniteFullFactors) :
    TheoremCStatement.statement :=
  JTGraphSpanSupportCriterion.theoremC_of_finite_full_factors (normalized_factors_iff.mp h)

/-- The normalized finite span evaluations may be contracted on weak covers
of the original finite full subcategories. -/
def NormalizedFiniteWeakCoverFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))
        (hP : Finite P.FullSubcategory),
        ∃ (B E : Cat.{0, 0}) (p : B ⥤ P.FullSubcategory) (F : B ⥤ E) (G : E ⥤ TargetComma Q),
          WeakEquivalence (nerveMap p) ∧ GW (pointMap (nerve E)) ∧
            NatTransZigzag (p ⋙ evaluation Q A P hP) (F ⋙ G)

/-- Weak covers permit arbitrary coherent choices while the conclusion
uses the unmodified Theorem C statement. -/
theorem theoremC_of_normalized_weak_cover_factors (h : NormalizedFiniteWeakCoverFactors) :
    TheoremCStatement.statement := by
  apply JTGraphSpanSupportCriterion.theoremC_of_support_nullhomotopies
  intro W hW x y Q A hA
  apply FiniteLastVertexSupport.of_finite_full_weak_cover_factors
  intro P hP
  obtain ⟨B, E, p, F, G, hp, hE, H⟩ := h W hW x y Q A hA P hP
  exact ⟨B, E, p, F, G, hp, hE,
    .trans _ _ _ (.rel _ _ ⟨Functor.whiskerLeft p (comparison Q A P hP)⟩) H⟩

end

end DaggerModels.PartII.JTStableSpanEvaluation
