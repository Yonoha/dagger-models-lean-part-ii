import DaggerModelsPartII.JTJointBeadContractionEvaluation
import DaggerModelsPartII.JTSupportedPathEvaluationNullhomotopy

/-! Nullhomotopy of each complete actual normalized bead contraction. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerNerveHomotopy CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointBeadContractionNullhomotopy

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
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

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

/-- The entire full-graph contraction of this actual bead is nullhomotopic
after singular realization, in its unchanged fixed point-target comma. -/
theorem evaluation_nullhomotopic :
    ∃ v : (Δ[0] : SSet.{0}) ⟶
        nerve (JTGraphFactoredPresentation.TargetComma
          (pointTarget W (jointCoefficient (Q := Q) j))),
      Nonempty (SSet.Homotopy
        (R.map (nerveMap
          (JTJointBeadContractionEvaluation.evaluation F j base D h₀ h₁ r hr)))
        (R.map (term (nerve (BoundaryNecklaceComma.Presentation
          (JTJointBeadContractionEvaluation.reduced F j base D h₀ h₁ r hr))) ≫ v))) := by
  exact JTSupportedPathEvaluationNullhomotopy.evaluation_nullhomotopic
    W (jointCoefficient (Q := Q) j)
    (JTJointBeadNormalizationDiagram.labels F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr ⋙ base ⋙ time)
    (JTJointBeadNormalizationSupport.support F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.incl F j base D h₀ h₁ r hr)
    (JTJointBeadContractionChoices.old_onSupport F j base D h₀ h₁ r hr)
    (JTJointBeadSupportedGraph.data F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.incl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadSupportedGraph.projection_trivialFibration F j base D h₀ h₁ r hr)

end
end DaggerModels.PartII.JTJointBeadContractionNullhomotopy
