import DaggerModelsPartII.JTJointBeadSupportedGraph
import DaggerModelsPartII.JTJointBeadContractionChoices
import DaggerModelsPartII.JTSupportedPathGraphEvaluation

/-! Full higher contraction evaluation of every normalized overlap bead. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointBeadContractionEvaluation

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTPointTargetEvaluationCone (pointTarget)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}

variable {A B : Type} [SmallCategory A] [SmallCategory B]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (base : B ⥤ A) (D : B ⥤ SimplexCategory)
variable (h₀ : ∀ {a b : B} (f : a ⟶ b), (D.map f).toOrderHom 0 = 0)
variable (h₁ : ∀ {a b : B} (f : a ⟶ b),
  (D.map f).toOrderHom (Fin.last (D.obj a).len) = Fin.last (D.obj b).len)
variable (r : ∀ b : B, (single (D.obj b).len).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app (base.obj b)) j j le_rfl).toSSet)
private abbrev native (b : B) :=
  r b ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app (base.obj b)) j
variable (hr : ∀ {a b : B} (f : a ⟶ b),
  (singleIso (D.obj a).len).inv ≫ native F j base D r a ≫
    ((codes L).map (base.map f)).map =
  std.map (D.map f) ≫ (singleIso (D.obj b).len).inv ≫ native F j base D r b)

private abbrev z := jointCoefficient (Q := Q) j
private abbrev I := JTJointBeadNormalizationDiagram.Index F j base D h₀ h₁ r hr
private abbrev labels := JTJointBeadNormalizationDiagram.labels F j base D h₀ h₁ r hr
private abbrev support := JTJointBeadNormalizationSupport.support F j base D h₀ h₁ r hr
private abbrev incl := JTJointBeadNormalizationSupport.incl F j base D h₀ h₁ r hr
private abbrev oldTime := JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr
  ⋙ base ⋙ time
private abbrev hs := JTJointBeadContractionChoices.old_onSupport F j base D h₀ h₁ r hr
private abbrev G := JTJointBeadSupportedGraph.data F j base D h₀ h₁ r hr

/-- The actual path-chain index of normalized overlap-bead labels. -/
abbrev Index := JTSupportedPathGraphData.Index W (z j)
  (labels F j base D h₀ h₁ r hr) (support F j base D h₀ h₁ r hr)
  (incl F j base D h₀ h₁ r hr) (hs F j base D h₀ h₁ r hr)

/-- The complete covered reduced cylinder of all higher contractions. -/
abbrev reduced := JTSupportedPathGraphEvaluation.reduced W (z j)
  (labels F j base D h₀ h₁ r hr) (oldTime F j base D h₀ h₁ r hr)
  (support F j base D h₀ h₁ r hr) (incl F j base D h₀ h₁ r hr)
  (hs F j base D h₀ h₁ r hr) (G F j base D h₀ h₁ r hr)

/-- Evaluate the whole actual higher contraction graph at the literal joint
in the unchanged fixed point-target comma. -/
def evaluation : BoundaryNecklaceComma.Presentation
    (reduced F j base D h₀ h₁ r hr) ⥤
      JTGraphFactoredPresentation.TargetComma (pointTarget W (z j)) :=
  JTSupportedPathGraphEvaluation.evaluation W (z j)
    (labels F j base D h₀ h₁ r hr) (oldTime F j base D h₀ h₁ r hr)
    (support F j base D h₀ h₁ r hr) (incl F j base D h₀ h₁ r hr)
    (hs F j base D h₀ h₁ r hr) (G F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.incl_mono F j base D h₀ h₁ r hr)

/-- Forget graph, path and chain choices, retaining the exact normalization index. -/
abbrev toNormalizationIndex : BoundaryNecklaceComma.Presentation
    (reduced F j base D h₀ h₁ r hr) ⥤ I F j base D h₀ h₁ r hr :=
  JTSupportedPathGraphEvaluation.toOriginal W (z j)
    (labels F j base D h₀ h₁ r hr) (oldTime F j base D h₀ h₁ r hr)
    (support F j base D h₀ h₁ r hr) (incl F j base D h₀ h₁ r hr)
    (hs F j base D h₀ h₁ r hr) (G F j base D h₀ h₁ r hr)

/-- The whole contraction presentation weakly covers the normalization index. -/
theorem toNormalizationIndex_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toNormalizationIndex F j base D h₀ h₁ r hr)) := by
  apply JTSupportedPathGraphEvaluation.toOriginal_weak W (z j)
    (labels F j base D h₀ h₁ r hr) (oldTime F j base D h₀ h₁ r hr)
    (support F j base D h₀ h₁ r hr) (incl F j base D h₀ h₁ r hr)
    (hs F j base D h₀ h₁ r hr) (G F j base D h₀ h₁ r hr)
  · exact JTJointBeadNormalizationSupport.incl_mono F j base D h₀ h₁ r hr
  · intro p
    exact JTJointBeadSupportedGraph.projection_trivialFibration F j base D h₀ h₁ r hr p
  · exact hW
  · exact JTJointBeadContractionChoices.code_pos F j base D h₀ h₁ r hr

/-- Retain precisely the original specified bead-chart object and arrows. -/
abbrev toCharts : BoundaryNecklaceComma.Presentation
    (reduced F j base D h₀ h₁ r hr) ⥤ B :=
  toNormalizationIndex F j base D h₀ h₁ r hr ⋙
    JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr

/-- The entire fixed-target contraction evaluation is based on a weak cover
of the original specified bead charts. -/
theorem toCharts_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toCharts F j base D h₀ h₁ r hr)) := by
  haveI : WeakEquivalence (nerveMap (toNormalizationIndex F j base D h₀ h₁ r hr)) :=
    toNormalizationIndex_weak F j base D h₀ h₁ r hr hW
  haveI : WeakEquivalence (nerveMap
      (JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr)) :=
    JTJointBeadNormalizationDiagram.toCharts_weak F j base D h₀ h₁ r hr hW
  change WeakEquivalence (nerveMap (toNormalizationIndex F j base D h₀ h₁ r hr) ≫
    nerveMap (JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr))
  infer_instance

end
end DaggerModels.PartII.JTJointBeadContractionEvaluation
