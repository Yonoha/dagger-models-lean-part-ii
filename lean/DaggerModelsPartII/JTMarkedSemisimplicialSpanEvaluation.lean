import DaggerModelsPartII.JTTargetJointMarks
import DaggerModelsPartII.JTSemisimplicialSpanEvaluation
import DaggerModelsPartII.JTGraphSpanEvaluation
import DaggerModelsPartII.JTRezkRecognitionFiniteFactor

/-! Exact original span evaluation with functorial marks at native target joints. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerNerveHomotopy
open DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTMarkedSemisimplicialSpanEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)

private abbrev C := TargetComma Q
/-- The full injective-phase cylinder evaluation before adding marks. -/
abbrev baseEvaluation : JTSemisimplicialSpanEvaluation.Presentation Q A ⥤ C Q :=
  JTSemisimplicialSpanEvaluation.evaluation Q A (JTGraphSpanEvaluation.fullEvaluation Q)

/-- Mark choices pulled back along the exact evaluated cylinder. -/
def marksDiagram : JTSemisimplicialSpanEvaluation.Presentation Q A ⥤ Cat.{0, 0} :=
  baseEvaluation Q A ⋙ JTTargetJointMarks.diagram W x y Q

/-- Cylinders equipped with functorial choices at every native target joint. -/
abbrev Marked := Grothendieck (marksDiagram Q A)

/-- Forget mark choices while retaining the full original cylinder. -/
abbrev forgetMarks : Marked Q A ⥤ JTSemisimplicialSpanEvaluation.Presentation Q A :=
  Grothendieck.forget (marksDiagram Q A)

set_option maxHeartbeats 700000 in
/-- The mark-choice projection is a nerve weak equivalence. -/
theorem forgetMarks_weak : WeakEquivalence (nerveMap (forgetMarks Q A)) := by
  apply GrothendieckContractibleFibers.projection_weak (marksDiagram Q A)
  intro P
  exact JTTargetJointMarks.diagram_point_GW W x y Q ((baseEvaluation Q A).obj P)

/-- Chosen terminal objects in the fibers give a strict section of the total projection. -/
private def terminalSection {I : Type} [SmallCategory I] (D : I ⥤ Cat.{0, 0})
    (t : ∀ i : I, D.obj i) (ht : ∀ i : I, IsTerminal (t i)) :
    I ⥤ Grothendieck D where
  obj i := ⟨i, t i⟩
  map f := ⟨f, (ht _).from _⟩
  map_id i := by
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber => exact (ht i).hom_ext _ _
  map_comp f g := by
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber => exact (ht _).hom_ext _ _

/-- The section returns each original base object and operator exactly. -/
private theorem terminalSection_forget {I : Type} [SmallCategory I] (D : I ⥤ Cat.{0, 0})
    (t : ∀ i : I, D.obj i) (ht : ∀ i : I, IsTerminal (t i)) :
    terminalSection D t ht ⋙ Grothendieck.forget D = 𝟭 I := rfl

private abbrev marks := JTTargetJointMarks.diagram W x y Q

private def greatestMark (U : C Q) : (marks Q).obj U :=
  JTTargetJointMarks.greatest U.hom.hom

private def greatestMark_terminal (U : C Q) : IsTerminal (greatestMark Q U) :=
  JTTargetJointMarks.greatestIsTerminal U.hom.hom


/-- Choose the greatest mark at every target joint, with a fiber arrow over
every original cylinder operator. -/
def greatestMarkSection : JTSemisimplicialSpanEvaluation.Presentation Q A ⥤ Marked Q A :=
  terminalSection (marksDiagram Q A)
    (fun P ↦ greatestMark Q ((baseEvaluation Q A).obj P))
    (fun P ↦ greatestMark_terminal Q ((baseEvaluation Q A).obj P))

/-- The marked section recovers every original object and arrow upon forgetting. -/
theorem greatestMarkSection_forget :
    greatestMarkSection Q A ⋙ forgetMarks Q A =
      𝟭 (JTSemisimplicialSpanEvaluation.Presentation Q A) :=
  terminalSection_forget (marksDiagram Q A) _ _

private theorem finite_hom_of_thin {I : Type} [SmallCategory I]
    (D : I ⥤ Cat.{0, 0})
    (hI : ∀ i j : I, Finite (i ⟶ j))
    (hD : ∀ i : I, Quiver.IsThin (D.obj i))
    (P P' : Grothendieck D) : Finite (P ⟶ P') := by
  letI : Finite (P.base ⟶ P'.base) := hI P.base P'.base
  letI (X Y : D.obj P'.base) : Subsingleton (X ⟶ Y) := hD P'.base X Y
  apply Finite.of_injective (f := fun f : P ⟶ P' ↦ f.base)
  intro f g h
  apply Grothendieck.ext f g h
  exact Subsingleton.elim _ _

/-- Marked cylinders have finite hom sets between fixed objects. -/
theorem marked_finite_hom (P P' : Marked Q A) : Finite (P ⟶ P') :=
  finite_hom_of_thin (marksDiagram Q A)
    (JTSemisimplicialSpanEvaluation.resolution_finite_hom Q A)
    (fun p ↦ JTTargetJointMarks.diagram_thin W x y Q ((baseEvaluation Q A).obj p)) P P'

/-- Evaluate marked cylinders by the same exact fixed-target evaluation. -/
def markedEvaluation : Marked Q A ⥤ C Q :=
  forgetMarks Q A ⋙ baseEvaluation Q A

/-- The marked resolution still projects to the original simplices. -/
def markedProjection : Marked Q A ⥤ A.toSSet.Elementsᵒᵖ :=
  forgetMarks Q A ⋙ JTSemisimplicialSpanEvaluation.projection Q A

/-- The composite projection is a nerve weak equivalence. -/
theorem markedProjection_weak : WeakEquivalence (nerveMap (markedProjection Q A)) := by
  letI : WeakEquivalence (nerveMap (forgetMarks Q A)) := forgetMarks_weak Q A
  letI : WeakEquivalence
      (nerveMap (JTSemisimplicialSpanEvaluation.projection Q A)) :=
    JTSemisimplicialSpanEvaluation.projection_weak Q A
  change WeakEquivalence (nerveMap (forgetMarks Q A) ≫
    nerveMap (JTSemisimplicialSpanEvaluation.projection Q A))
  infer_instance

/-- The exact last-vertex comparison lifts to all marked cylinders. -/
def markedComparison : markedEvaluation Q A ⟶ markedProjection Q A ⋙
    NerveSimplexResolutionHomotopy.lastVertexOnSubcomplex (C Q) A := by
  let p := JTSemisimplicialSpanEvaluation.projection Q A
  let l := NerveSimplexResolutionHomotopy.lastVertexOnSubcomplex (C Q) A
  exact Functor.whiskerLeft (forgetMarks Q A)
      (JTSemisimplicialSpanEvaluation.comparison Q A
        (JTGraphSpanEvaluation.fullComparison Q)) ≫
    eqToHom (Functor.assoc (forgetMarks Q A) p l).symm

/-- Finite-support contractions on marked cylinders contract the original inclusion. -/
theorem inclusion_nullhomotopic (hA : A.toSSet.IsFinite)
    (hS : FiniteLastVertexSupport.SupportNullhomotopies (markedEvaluation Q A)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (C Q),
      Nonempty (SSet.Homotopy (R.map A.ι)
        (R.map (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ v))) := by
  letI := markedProjection_weak Q A
  exact FiniteLastVertexSupport.inclusion_nullhomotopic A
    (markedProjection Q A) (markedEvaluation Q A) hA (markedComparison Q A) hS

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- Support nullhomotopies on marked cylinders imply Theorem C. -/
theorem theoremC_of_marked_support_nullhomotopies
    (h : ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
        FiniteLastVertexSupport.SupportNullhomotopies (markedEvaluation Q A)) :
    TheoremCStatement.statement := by
  apply JTRezkRecognitionFiniteFactor.theoremC_of_finite_comma_nullhomotopies
  intro W hW x y Q A hA
  exact inclusion_nullhomotopic Q A hA (h W hW x y Q A hA)

end
end DaggerModels.PartII.JTMarkedSemisimplicialSpanEvaluation
