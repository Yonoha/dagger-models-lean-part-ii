import DaggerModelsPartII.JTGraphVariableMarkedSourceFamily
import DaggerModelsPartII.JTGraphVariableTotalFamilyEvaluation
import DaggerModelsPartII.JTParametrizedTargetFamilyReindexEvaluation

/-!
The actual marked weak resolution retains the complete original internal
necklace at every index. Compare its reindexed family evaluation to the
unchanged original diagram by the existing full reindexing comparison and
exact global evaluation, without a new natural-choice or raw premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableMarkedSourceEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableResolutionCategory (totalCode)
open JTGraphVariableMarkedSourceFamily (Marked toFamilyIndex family projection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {B : Type} [SmallCategory B] (original : B ⥤ TargetComma Q)

private abbrev labels := toFamilyIndex original ⋙
  JTGraphVariableResolutionCategory.totalLabels Q
private abbrev time := toFamilyIndex original ⋙
  JTGraphVariableTotalParametrizedFamily.time Q
private abbrev cylinders := JTParametrizedTargetFamilies.cylinders
  (L := labels original) (time := time original)

/-- Keep the complete old internal traversal after the actual weak-cover maps. -/
def traversal : (toFamilyIndex original ⋙ totalCode Q) ⋙
    BoundaryNecklaceComma.necklaceUnder ⟶ 𝟭 (Marked original) ⋙ cylinders original :=
  Functor.whiskerLeft (toFamilyIndex original)
    (JTGraphVariableTotalFamilyEvaluation.traversal Q)

/-- Each marked index retains its original complete internal necklace. -/
def sectionFunctor : Marked original ⥤ JTParametrizedTargetFamilies.Presentation
    (L := labels original) (time := time original) :=
  JTTargetCommaPullback.assemble (cylinders original) (𝟭 (Marked original))
    (toFamilyIndex original ⋙ totalCode Q) (traversal original)

/-- Forgetting the reindexing keeps exactly the old global section, including
all original operators and every internal necklace. -/
theorem reindex_section : sectionFunctor original ⋙
    JTParametrizedTargetFamilies.reindexPresentation
      (L := JTGraphVariableResolutionCategory.totalLabels Q)
      (time := JTGraphVariableTotalParametrizedFamily.time Q) (toFamilyIndex original) =
      toFamilyIndex original ⋙ JTGraphVariableTotalFamilyEvaluation.sectionFunctor Q := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply JTTargetCommaPullback.operator_ext
  · rfl
  · rfl

private theorem evaluation_target :
    (sectionFunctor original ⋙
      JTParametrizedTargetFamilies.reindexPresentation
      (L := JTGraphVariableResolutionCategory.totalLabels Q)
      (time := JTGraphVariableTotalParametrizedFamily.time Q) (toFamilyIndex original)) ⋙
        JTParametrizedTargetFamilies.evaluate
          (JTGraphVariableTotalParametrizedFamily.family Q) =
      toFamilyIndex original ⋙ JTGraphVariableExactEvaluation.evaluation Q := by
  rw [reindex_section, Functor.assoc,
    JTGraphVariableTotalFamilyEvaluation.section_evaluate]

/-- The full marked-family section evaluation in the exact original comma. -/
abbrev evaluation := sectionFunctor original ⋙
  JTParametrizedTargetFamilies.evaluate (family original)

/-- Its comparison to the old exact evaluation uses the complete reindexing
natural transformation, not just equality of raw values or individual objects. -/
def comparisonToTotal : evaluation original ⟶
    toFamilyIndex original ⋙ JTGraphVariableExactEvaluation.evaluation Q :=
  Functor.whiskerLeft (sectionFunctor original)
      (JTParametrizedTargetFamilies.compareEvaluation_reindex
        (JTGraphVariableTotalParametrizedFamily.family Q) (toFamilyIndex original)) ≫
    (Functor.associator (sectionFunctor original)
      (JTParametrizedTargetFamilies.reindexPresentation
      (L := JTGraphVariableResolutionCategory.totalLabels Q)
      (time := JTGraphVariableTotalParametrizedFamily.time Q) (toFamilyIndex original))
      (JTParametrizedTargetFamilies.evaluate
        (JTGraphVariableTotalParametrizedFamily.family Q))).inv ≫
    eqToHom (evaluation_target original)

/-- Every original diagram has this actual marked weak resolution and a
natural comparison of its full section evaluation to that same diagram. -/
def comparison : evaluation original ⟶ projection original ⋙ original :=
  comparisonToTotal original ≫ Functor.whiskerLeft (toFamilyIndex original)
    (JTGraphVariableExactEvaluation.comparison Q)

end
end DaggerModels.PartII.JTGraphVariableMarkedSourceEvaluation
