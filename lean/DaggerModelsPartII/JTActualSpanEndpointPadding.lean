import DaggerModelsPartII.JTEndpointPaddedDecoratedEvaluation
import DaggerModelsPartII.JTGraphSpanSupportCriterion
import DaggerModelsPartII.JTNativeEndpointPaddingPresentation
import DaggerModelsPartII.JTActualSpanFamilySection
import DaggerModelsPartII.JTParametrizedTargetFamilyReindexEvaluation

/-! Apply the weak native endpoint padding to the actual finite-span evaluations. -/

set_option autoImplicit false
set_option maxHeartbeats 520000

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualSpanEndpointPadding

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTActualSpanFamilySection (actualFamily actualSpans originalEvaluation_eq originalComparison
  parametrizedFullComparison)
open JTParametrizedTargetFamilies (codes cylinders evaluate reindexPresentation
  compareEvaluation_reindex)
open BoundaryNecklaceComma (fiberDiagram)
open JTNativeEndpointPadding (projectPresentation projectPresentation_weak)

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

private abbrev J := actualSpans Q A P
private abbrev labels := J Q A P ⋙ JTGraphSpanLift.spanLabels Q
private abbrev time := J Q A P ⋙ JTGraphSpanLift.time Q
private abbrev code := codes (labels Q A P)
private abbrev F := actualFamily Q A P
private abbrev underlying := cylinders (L := labels Q A P) (time := time Q A P)
private abbrev padded := JTNativeEndpointPadding.cylinders (code Q A P) (time Q A P)

/-- Retain all internal necklaces of the padded actual finite cylinders. -/
abbrev Presentation := BoundaryNecklaceComma.Presentation (padded Q A P)

private abbrev unpad := projectPresentation (code Q A P) (time Q A P)

/-- The padded full presentation projects to the chosen original finite span. -/
def projection : Presentation Q A P ⥤ P.FullSubcategory :=
  Grothendieck.forget (fiberDiagram (padded Q A P))

/-- A direct weak cover, using the contractible native fibers of the padded cylinders. -/
theorem projection_weak : WeakEquivalence (nerveMap (projection Q A P)) :=
  GrothendieckContractibleFibers.projection_weak _
    (fun i ↦ JTHomotopyTargetComma.fiber_point_GW_at
      (JTNativeEndpointPadding.pad.obj ((code Q A P).obj i)) ((time Q A P).obj i))

/-- The projection to the original cylinders keeps their exact fixed-target evaluation. -/
def evaluation : Presentation Q A P ⥤ TargetComma Q :=
  unpad Q A P ⋙ evaluate (F Q A P)

private abbrev tailFunctor := JTGraphSpanFamily.tail (TargetComma Q)
private abbrev tail := J Q A P ⋙ tailFunctor (Q := Q)

private abbrev originalEval :=
  P.ι ⋙ JTSemisimplicialSpanEvaluation.evaluation Q A (JTGraphSpanEvaluation.fullEvaluation Q)

private def originalToTail :
    projection Q A P ⋙ originalEval Q A P ⟶ projection Q A P ⋙ tail Q A P :=
  Functor.whiskerLeft (projection Q A P)
    (eqToHom (originalEvaluation_eq Q A P).symm ≫ originalComparison Q A P)

private def pasteToTail {B C D Y : Type}
    [SmallCategory B] [SmallCategory C] [SmallCategory D] [SmallCategory Y]
    {e : B ⥤ Y} {H : B ⥤ C} {F : C ⥤ Y} {p : C ⥤ D} {k : D ⥤ Y}
    {l : B ⥤ D} (h : e ⟶ H ⋙ F) (a : F ⟶ p ⋙ k) (hl : H ⋙ p = l) :
    e ⟶ l ⋙ k :=
  h ≫ Functor.whiskerLeft H a ≫
    eqToHom ((Functor.assoc H p k).symm.trans (congrArg (· ⋙ k) hl))

private theorem reindex_forget {I K : Type} [SmallCategory I] [SmallCategory K]
    (F : I ⥤ Cat.{0, 0}) (G : K ⥤ I) :
    Grothendieck.pre F G ⋙ Grothendieck.forget F =
      Grothendieck.forget (G ⋙ F) ⋙ G := rfl

open JTParametrizedTargetFamilies (Family)

private def compareFamilyToTail {I K : Type} [SmallCategory I] [SmallCategory K]
    {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {t : I ⥤ SimplexCategory}
    (F : Family Q L t) (G : K ⥤ I) (k : I ⥤ TargetComma Q)
    (h : evaluate F ⟶ Grothendieck.forget (fiberDiagram (cylinders (L := L) (time := t))) ⋙ k) :
    evaluate (F.precomp G) ⟶ Grothendieck.forget
      (fiberDiagram (cylinders (L := G ⋙ L) (time := G ⋙ t))) ⋙ G ⋙ k := by
  let D := fiberDiagram (cylinders (L := L) (time := t))
  let p := Grothendieck.forget (G ⋙ D)
  let r := Grothendieck.pre D G
  let e : evaluate (F.precomp G) ⟶ r ⋙ evaluate F := compareEvaluation_reindex F G
  exact pasteToTail e h (reindex_forget D G) ≫ eqToHom (Functor.assoc p G k)

private def compareFiniteToTail :
    evaluate (F Q A P) ⟶
      Grothendieck.forget (fiberDiagram (underlying Q A P)) ⋙ tail Q A P :=
  compareFamilyToTail Q (JTGraphSpanLift.spanFamily Q) (J Q A P)
    (tailFunctor (Q := Q)) (parametrizedFullComparison Q)

/-- Pad the finite cylinders before comparing to the same original final vertex. -/
def compareToTail :
    evaluation Q A P ⟶ projection Q A P ⋙ tail Q A P := by
  let H := unpad Q A P
  let p := Grothendieck.forget (fiberDiagram (underlying Q A P))
  let T := tail Q A P
  exact Functor.whiskerLeft H (compareFiniteToTail Q A P) ≫
    eqToHom (Functor.assoc H p T).symm ≫
    eqToHom (congrArg (· ⋙ T)
      (JTNativeEndpointPadding.projectPresentation_forget (code Q A P) (time Q A P)))

/-- All internal necklaces of the padded finite cylinders compare to the original evaluation. -/
theorem original_comparison :
    NatTransZigzag (projection Q A P ⋙ originalEval Q A P) (evaluation Q A P) :=
  .trans _ _ _ (.rel _ _ ⟨originalToTail Q A P⟩) (.symm _ _ (.rel _ _ ⟨compareToTail Q A P⟩))

section NativeTarget

open NecklaceCylinderAugmentation (augmentation)

variable {targetTime : P.FullSubcategory ⥤ SimplexCategory} (a : time Q A P ⟶ targetTime)

private abbrev nativeCollapse : code Q A P ⟶ (Functor.const P.FullSubcategory).obj Q.code :=
  (F Q A P).collapse

/-- The actual padded finite source lands in the complete padded target
cylinder, with any prescribed natural time operator. -/
def toPaddedTarget :
    padded Q A P ⟶
      ((Functor.const P.FullSubcategory).obj (JTNativeEndpointPadding.pad.obj Q.code)).prod'
        targetTime ⋙ NecklaceCylinderJointDiagram.cylinderUnder :=
  JTNativeEndpointPadding.mapToPaddedTarget (code Q A P) (time Q A P) (nativeCollapse Q A P) a

/-- Its native map after forgetting the two target beads is the original
complete native map after forgetting the two source beads. -/
theorem toPaddedTarget_native (i : P.FullSubcategory) :
    ((toPaddedTarget Q A P a).app i).right ≫
        augmentation (JTNativeEndpointPadding.pad.obj Q.code) (targetTime.obj i) ≫
        (JTNativeEndpointPadding.collapse.app Q.code).map =
      ((JTNativeEndpointPadding.collapseCylinders (code Q A P) (time Q A P)).app i).right ≫
        augmentation ((code Q A P).obj i) ((time Q A P).obj i) ≫
        ((nativeCollapse Q A P).app i).map :=
  JTNativeEndpointPadding.mapToPaddedTarget_native (code Q A P) (time Q A P)
    (nativeCollapse Q A P) a i

end NativeTarget

private abbrev decoratedFamily : Family Q
    (JTEndpointPaddedDecoratedFamily.labels (labels Q A P)) (time Q A P) :=
  JTEndpointPaddedDecoratedFamily.family (F Q A P)

/-- Evaluate the padded source using the pulled-back padded decorated labels. -/
def decoratedEvaluation : Presentation Q A P ⥤ TargetComma Q :=
  @evaluate P.FullSubcategory _ W x y Q
    (JTEndpointPaddedDecoratedFamily.labels (labels Q A P)) (time Q A P) (decoratedFamily Q A P)

/-- Collapsing the padded decorated label gives the evaluated native padding. -/
def compareDecoratedEvaluation : decoratedEvaluation Q A P ⟶ evaluation Q A P :=
  @JTEndpointPaddedDecoratedFamily.compareEvaluation P.FullSubcategory _
    W x y Q (labels Q A P) (time Q A P) (F Q A P)

/-- The decorated padded evaluation compares to the original finite-span evaluation. -/
theorem original_comparison_decorated :
    NatTransZigzag (projection Q A P ⋙ originalEval Q A P) (decoratedEvaluation Q A P) :=
  .trans _ _ _ (original_comparison Q A P)
    (.symm _ _ (.rel _ _ ⟨compareDecoratedEvaluation Q A P⟩))

section Criterion

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The factor condition for the padded cover of every actual finite span. -/
def PaddedFiniteFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A)),
        Finite P.FullSubcategory →
        ∃ (E : Cat.{0, 0}) (F : Presentation Q A P ⥤ E) (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧ NatTransZigzag (evaluation Q A P) (F ⋙ G)

/-- Weakly contractible factors on the padded cover imply the original Theorem C. -/
theorem theoremC_of_padded_factors (h : PaddedFiniteFactors) : TheoremCStatement.statement := by
  apply JTGraphSpanSupportCriterion.theoremC_of_support_nullhomotopies
  intro W hW x y Q A hA
  apply FiniteLastVertexSupport.of_finite_full_weak_cover_factors
  intro P hP
  obtain ⟨E, F, G, hE, e⟩ := h W hW x y Q A hA P hP
  exact ⟨Cat.of (Presentation Q A P), E, projection Q A P, F, G,
    projection_weak Q A P, hE, .trans _ _ _ (original_comparison Q A P) e⟩

/-- The factor condition for the padded source and padded decorated labels together. -/
def DecoratedPaddedFiniteFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A)),
        Finite P.FullSubcategory →
        ∃ (E : Cat.{0, 0}) (F : Presentation Q A P ⥤ E) (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧ NatTransZigzag (decoratedEvaluation Q A P) (F ⋙ G)

/-- Weakly contractible factors of the fully padded evaluations imply the original Theorem C. -/
theorem theoremC_of_decorated_padded_factors
    (h : DecoratedPaddedFiniteFactors) : TheoremCStatement.statement := by
  apply theoremC_of_padded_factors
  intro W hW x y Q A hA P hP
  obtain ⟨E, F, G, hE, e⟩ := h W hW x y Q A hA P hP
  exact ⟨E, F, G, hE, .trans _ _ _
    (.symm _ _ (.rel _ _ ⟨compareDecoratedEvaluation Q A P⟩)) e⟩

end Criterion

end
end DaggerModels.PartII.JTActualSpanEndpointPadding
