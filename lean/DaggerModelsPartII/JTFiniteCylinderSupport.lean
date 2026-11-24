import DaggerModelsPartII.JTFiniteSourceResolution
import DaggerModelsPartII.FiniteLastVertexSupport
import DaggerModelsPartII.JTFiniteSubcomplexVariableResolution

/-! Finite simplicial support in the actual restricted cylinder evaluation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteCylinderSupport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeTransport (resolutionDiagram)
open JTGraphVariableResolutionCategory (toPresentation totalComparison)
open NerveSimplexResolutionHomotopy (lastVertexOnSubcomplex comparisonOnSubcomplex)
open SimplicialResolutionFunctor (augmentation augmentation_weak elementsProjection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev toPoint (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex) (n : ℕ)

private abbrev last := lastVertexOnSubcomplex (TargetComma Q) A
private abbrev I := BoundedSimplex.inclusion A.toSSet n

/-- Resolve the bounded last-vertex diagram using only native collapses
from its own arrows. -/
abbrev diagram := FiniteSourceSlice.diagram (I Q A n ⋙ last Q A)

private abbrev π := Grothendieck.forget (diagram Q A n) ⋙ I Q A n
private def toTotal : Grothendieck (diagram Q A n) ⥤
    Grothendieck (resolutionDiagram Q) :=
  FiniteSourceSlice.inclusion (I Q A n ⋙ last Q A) ⋙
    Grothendieck.pre (resolutionDiagram Q) (I Q A n ⋙ last Q A)

/-- The evaluation is the original fixed-target evaluation on those cylinders. -/
def evaluation : Grothendieck (diagram Q A n) ⥤ TargetComma Q :=
  toTotal Q A n ⋙ toPresentation Q ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse

private theorem projection_weak (hn : ∀ s : A.toSSet.N, s.dim ≤ n) :
    WeakEquivalence (nerveMap (π Q A n)) := by
  letI := BoundedSimplex.inclusion_weak hn
  letI := FiniteSourceSlice.projection_weak (I Q A n ⋙ last Q A)
  change WeakEquivalence (nerveMap (Grothendieck.forget (diagram Q A n)) ≫ nerveMap (I Q A n))
  infer_instance

private def comparison : evaluation Q A n ⟶ π Q A n ⋙ last Q A :=
  Functor.whiskerLeft (toTotal Q A n) (totalComparison Q)

/-- The contraction condition uses the actual finite simplicial support
and keeps its original time and internal-necklace operators. -/
abbrev SupportNullhomotopies : Prop := FiniteLastVertexSupport.SupportNullhomotopies (evaluation Q A n)

/-- A contraction on each finite support suffices to contract the literal
inclusion of the original finite subcomplex. -/
theorem inclusion_nullhomotopic (hA : A.toSSet.IsFinite)
    (hn : ∀ s : A.toSSet.N, s.dim ≤ n) (h : SupportNullhomotopies Q A n) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
      Nonempty (SSet.Homotopy (R.map A.ι) (R.map (toPoint A.toSSet ≫ v))) := by
  letI := projection_weak Q A n hn
  exact FiniteLastVertexSupport.inclusion_nullhomotopic A (π Q A n) (evaluation Q A n)
    hA (comparison Q A n) h

/-- The original four-link Theorem C follows from contraction on finite
supports, with the original resolved evaluation on each such support. -/
theorem theoremC_of_support_nullhomotopies
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
        ∃ n, (∀ s : A.toSSet.N, s.dim ≤ n) ∧ SupportNullhomotopies Q A n) :
    TheoremCStatement.statement := by
  apply JTRezkRecognitionFiniteFactor.theoremC_of_finite_comma_nullhomotopies
  intro W hW x y Q A hA
  obtain ⟨n, hn, hS⟩ := h W hW x y Q A hA
  exact inclusion_nullhomotopic Q A n hA hn hS

end
end DaggerModels.PartII.JTFiniteCylinderSupport
