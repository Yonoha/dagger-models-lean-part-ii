import DaggerModelsPartII.JTStableSpanEvaluation

/-! The parametrized span family and its chosen necklaces on each original finite support. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualSpanFamilySection

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
variable (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))

private abbrev C := TargetComma Q
private abbrev S := JTGraphCylinderSimplexSpan.SpanIndex (C Q)
private abbrev F := JTGraphCylinderSimplexSpan.fibers (C Q)
  (JTGraphCylinderSpanProjection.nativeCode Q)
private abbrev O := HomSpanRestriction.map ((CategoryOfElements.map A.ι).op)

/-- The full original internal-necklace object of every finite-support point. -/
def originalPresentation : P.FullSubcategory ⥤ Grothendieck (F Q) :=
  P.ι ⋙ JTGraphSpanSemisimplicial.cover A (JTGraphCylinderSpanProjection.nativeCode Q) ⋙
    Grothendieck.pre (F Q) (O Q A)

/-- The actual span index underlying the chosen internal necklaces. -/
def actualSpans : P.FullSubcategory ⥤ S Q :=
  originalPresentation Q A P ⋙ Grothendieck.forget (F Q)

/-- The exact family, based on the actual spans and retaining their native operators. -/
def actualFamily :=
  (JTGraphSpanLift.spanFamily Q).precomp (actualSpans Q A P)

/-- Pull each chosen Grothendieck object back to its own base. -/
private def pullbackSection {B I : Type} [SmallCategory B] [SmallCategory I]
    (D : I ⥤ Cat.{0, 0}) (H : B ⥤ Grothendieck D) :
    B ⥤ Grothendieck ((H ⋙ Grothendieck.forget D) ⋙ D) where
  obj b := ⟨b, (H.obj b).fiber⟩
  map f := ⟨f, (H.map f).fiber⟩
  map_id b := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simpa using Grothendieck.congr (H.map_id b)
  map_comp f g := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simpa using Grothendieck.congr (H.map_comp f g)

/-- A natural section preserving every chosen internal necklace and its operators. -/
def chosenInternalNecklaces :
    P.FullSubcategory ⥤ Grothendieck ((actualSpans Q A P) ⋙ F Q) :=
  pullbackSection (F Q) (originalPresentation Q A P)

theorem chosenInternalNecklaces_original :
    chosenInternalNecklaces Q A P ⋙
      Grothendieck.pre (F Q) (actualSpans Q A P) =
        originalPresentation Q A P := by
  rfl

private theorem actualFibers_eq :
    actualSpans Q A P ⋙ F Q =
      BoundaryNecklaceComma.fiberDiagram
        (JTParametrizedTargetFamilies.cylinders
          (L := (actualSpans Q A P) ⋙ JTGraphSpanLift.spanLabels Q)
          (time := (actualSpans Q A P) ⋙ JTGraphSpanLift.time Q)) := by
  let g := actualSpans Q A P
  let D := JTParametrizedTargetFamilies.cylinders
    (L := JTGraphSpanLift.spanLabels Q) (time := JTGraphSpanLift.time Q)
  have h : D = JTGraphCylinderSimplexSpan.index (C Q)
      (JTGraphCylinderSpanProjection.nativeCode Q) ⋙
        NecklaceCylinderJointDiagram.cylinderUnder :=
    JTGraphSpanLift.cylinders_eq Q
  calc
    g ⋙ F Q = g ⋙ ((JTGraphCylinderSimplexSpan.index (C Q)
        (JTGraphCylinderSpanProjection.nativeCode Q) ⋙
          NecklaceCylinderJointDiagram.cylinderUnder) ⋙
            BoundaryNecklaceComma.diagram) := by
      unfold F JTGraphCylinderSimplexSpan.fibers JTGraphCylinderFiberDiagram.diagram
      rw [CategoryTheory.Functor.assoc]
    _ = g ⋙ (D ⋙ BoundaryNecklaceComma.diagram) := by rw [h]
    _ = BoundaryNecklaceComma.fiberDiagram
        (JTParametrizedTargetFamilies.cylinders
          (L := g ⋙ JTGraphSpanLift.spanLabels Q)
          (time := g ⋙ JTGraphSpanLift.time Q)) := by
      rfl

/-- The selected internal necklaces in the parametrized family presentation. -/
def actualSection : P.FullSubcategory ⥤
    JTParametrizedTargetFamilies.Presentation
      (L := (actualSpans Q A P) ⋙ JTGraphSpanLift.spanLabels Q)
      (time := (actualSpans Q A P) ⋙ JTGraphSpanLift.time Q) :=
  chosenInternalNecklaces Q A P ⋙
    Grothendieck.map (eqToHom (actualFibers_eq Q A P))

theorem actualSection_projection :
    actualSection Q A P ⋙ Grothendieck.forget
      (BoundaryNecklaceComma.fiberDiagram
        (JTParametrizedTargetFamilies.cylinders
          (L := (actualSpans Q A P) ⋙ JTGraphSpanLift.spanLabels Q)
          (time := (actualSpans Q A P) ⋙ JTGraphSpanLift.time Q))) =
      𝟭 P.FullSubcategory := by
  rfl

/-- The unnormalized evaluation on the chosen original internal necklaces is exactly
the parametrized evaluation before any finite normalization. -/
theorem originalPresentation_parametrized_evaluation :
    (originalPresentation Q A P ⋙
        JTGraphSpanEvaluation.parametrizedPresentationMap Q) ⋙
          JTParametrizedTargetFamilies.evaluate (JTGraphSpanLift.spanFamily Q) =
      originalPresentation Q A P ⋙ JTGraphSpanEvaluation.fullEvaluation Q := by
  rw [CategoryTheory.Functor.assoc]
  exact congrArg (originalPresentation Q A P ⋙ ·)
    (JTGraphSpanEvaluation.evaluate_parametrizedPresentationMap Q)


private abbrev D := JTParametrizedTargetFamilies.cylinders
  (L := JTGraphSpanLift.spanLabels Q) (time := JTGraphSpanLift.time Q)

private theorem globalFibers_eq : F Q = BoundaryNecklaceComma.fiberDiagram (D Q) := by
  let i := JTGraphCylinderSimplexSpan.index (C Q)
    (JTGraphCylinderSpanProjection.nativeCode Q)
  have h : D Q = i ⋙ NecklaceCylinderJointDiagram.cylinderUnder :=
    JTGraphSpanLift.cylinders_eq Q
  calc
    F Q = (i ⋙ NecklaceCylinderJointDiagram.cylinderUnder) ⋙
        BoundaryNecklaceComma.diagram := by
      unfold F JTGraphCylinderSimplexSpan.fibers JTGraphCylinderFiberDiagram.diagram
      rw [CategoryTheory.Functor.assoc]
    _ = D Q ⋙ BoundaryNecklaceComma.diagram :=
      congrArg (· ⋙ BoundaryNecklaceComma.diagram) h.symm
    _ = BoundaryNecklaceComma.fiberDiagram (D Q) := rfl

/-- Inverse to the exact global parametrized presentation identification. -/
def fromParametrizedPresentation :
    JTParametrizedTargetFamilies.Presentation
      (L := JTGraphSpanLift.spanLabels Q) (time := JTGraphSpanLift.time Q) ⥤
      Grothendieck (F Q) :=
  Grothendieck.map (eqToHom (globalFibers_eq Q).symm)

private theorem originalFibers_eq :
    BoundaryNecklaceComma.fiberDiagram
      (JTGraphSpanLift.originalCylinders Q) = F Q := by
  unfold F JTGraphCylinderSimplexSpan.fibers JTGraphCylinderFiberDiagram.diagram
    BoundaryNecklaceComma.fiberDiagram JTGraphSpanLift.originalCylinders
  exact CategoryTheory.Functor.assoc _ _ _

private theorem map_eqToHom_cycle {I : Type} [SmallCategory I]
    {D₀ D₁ D₂ : I ⥤ Cat.{0, 0}}
    (h₀ : D₀ = D₁) (h₁ : D₁ = D₂) (h₂ : D₂ = D₀) :
    Grothendieck.map (eqToHom h₀ ≫ eqToHom h₁ ≫ eqToHom h₂) = 𝟭 _ := by
  cases h₀
  cases h₁
  cases h₂
  simp only [eqToHom_refl, Category.id_comp, Grothendieck.map_id_eq]

private theorem fromParametrizedPresentation_inverse :
    fromParametrizedPresentation Q ⋙
      JTGraphSpanEvaluation.parametrizedPresentationMap Q =
      𝟭 _ := by
  unfold fromParametrizedPresentation
    JTGraphSpanEvaluation.parametrizedPresentationMap
  change Grothendieck.map (eqToHom (globalFibers_eq Q).symm) ⋙
      Grothendieck.map (eqToHom (originalFibers_eq Q).symm) ⋙
        Grothendieck.map (eqToHom
          (congrArg BoundaryNecklaceComma.fiberDiagram
            (JTGraphSpanLift.cylinders_eq Q).symm)) = 𝟭 _
  rw [← Grothendieck.map_comp_eq, ← Grothendieck.map_comp_eq]
  exact map_eqToHom_cycle _ _ _

theorem fromParametrizedPresentation_evaluation :
    fromParametrizedPresentation Q ⋙ JTGraphSpanEvaluation.fullEvaluation Q =
      JTParametrizedTargetFamilies.evaluate (JTGraphSpanLift.spanFamily Q) := by
  let M := JTGraphSpanEvaluation.parametrizedPresentationMap Q
  let E := JTParametrizedTargetFamilies.evaluate (JTGraphSpanLift.spanFamily Q)
  have h : M ⋙ E = JTGraphSpanEvaluation.fullEvaluation Q :=
    JTGraphSpanEvaluation.evaluate_parametrizedPresentationMap Q
  calc
    fromParametrizedPresentation Q ⋙ JTGraphSpanEvaluation.fullEvaluation Q =
        fromParametrizedPresentation Q ⋙ (M ⋙ E) := congrArg _ h.symm
    _ = (fromParametrizedPresentation Q ⋙ M) ⋙ E :=
      (CategoryTheory.Functor.assoc _ _ _).symm
    _ = E := by rw [fromParametrizedPresentation_inverse]; exact Functor.id_comp _

private theorem fromParametrizedPresentation_base :
    fromParametrizedPresentation Q ⋙ Grothendieck.forget (F Q) =
      Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (D Q)) := by
  exact Grothendieck.functor_comp_forget

/-- The original parametrized evaluation on all internal necklaces compares
to the actual span tail before finite normalization. -/
def parametrizedFullComparison :
    JTParametrizedTargetFamilies.evaluate (JTGraphSpanLift.spanFamily Q) ⟶
      Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (D Q)) ⋙
        JTGraphSpanFamily.tail (C Q) :=
  eqToHom (fromParametrizedPresentation_evaluation Q).symm ≫
    Functor.whiskerLeft (fromParametrizedPresentation Q)
      (JTGraphSpanEvaluation.fullComparison Q) ≫
        eqToHom (by
          rw [← CategoryTheory.Functor.assoc,
            fromParametrizedPresentation_base])

private abbrev inclusion := P.ι
private abbrev cover := JTGraphSpanSemisimplicial.cover A (JTGraphCylinderSpanProjection.nativeCode Q)
private abbrev pre := Grothendieck.pre (F Q) (O Q A)
private abbrev eval := JTGraphSpanEvaluation.fullEvaluation Q

/-- The exact finite-source evaluation has only been reassociated. -/
theorem originalEvaluation_eq :
    originalPresentation Q A P ⋙ eval Q =
      P.ι ⋙ JTSemisimplicialSpanEvaluation.evaluation Q A (eval Q) :=
  (Functor.assoc (inclusion Q A P) (cover Q A ⋙ pre Q A) (eval Q)).trans
    (congrArg (inclusion Q A P ⋙ ·) (Functor.assoc (cover Q A) (pre Q A) (eval Q)))

/-- Explicit comparison of the unnormalized chosen evaluation to the original span tail. -/
def originalComparison :
    originalPresentation Q A P ⋙ JTGraphSpanEvaluation.fullEvaluation Q ⟶
      actualSpans Q A P ⋙ JTGraphSpanFamily.tail (C Q) :=
  Functor.whiskerLeft (originalPresentation Q A P)
    (JTGraphSpanEvaluation.fullComparison Q) ≫
      eqToHom (CategoryTheory.Functor.assoc
        (originalPresentation Q A P) (Grothendieck.forget (F Q))
          (JTGraphSpanFamily.tail (C Q))).symm

/-- Reindex the full original span comparison over any family of actual spans. -/
def familyOriginalComparison {B : Type} [SmallCategory B] (g : B ⥤ S Q) :
    Grothendieck.pre (F Q) g ⋙ JTGraphSpanEvaluation.fullEvaluation Q ⟶
      (Grothendieck.forget (g ⋙ F Q) ⋙ g) ⋙ JTGraphSpanFamily.tail (C Q) :=
  Functor.whiskerLeft (Grothendieck.pre (F Q) g)
    (JTGraphSpanEvaluation.fullComparison Q) ≫
      eqToHom (by
        rw [← CategoryTheory.Functor.assoc]
        rfl)


end
end DaggerModels.PartII.JTActualSpanFamilySection
