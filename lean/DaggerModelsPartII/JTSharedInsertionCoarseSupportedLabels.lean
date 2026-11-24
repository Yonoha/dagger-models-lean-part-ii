import DaggerModelsPartII.JTSharedInsertionCoarseWhiskeredData

/-!
# The supported coefficient path for the actual coarse insertion label

All support equations and corrected surroundings are derived from the original
Family and joint. The existing full path-choice and two chain covers retain all
higher simplices. Their projection is weak over the exact original insertion
choices under the existing injective fibrancy hypothesis, including zero-width
charts because the corrected middle has its two native padding edges.
This is not a weak cover of Marked or the original finite span category.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseSupportedLabels

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private theorem padded_positive (T : NecklaceCode) :
    0 < (wedge (single 1) (wedge T (single 1))).len := by
  change 0 < 1 + (T.len + 1)
  omega

private theorem codesReindex {I : Type} [SmallCategory I] (W : Source)
    (x z y : Vertex W) (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
    (S : I ⥤ SimplexCategory) (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees M)
    (hs : ∀ p : I, SSet.stdSimplex.map (u.app p) ≫
      JTSupportedOrderedCoefficientChoices.old W z M p =
        JTSupportedOrderedCoefficientChoices.supportedConstant W z M S p)
    (P R : I ⥤ NecklaceCode) (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
    (C : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (e : JTSupportedPathWhiskeredGraph.oldLabels W x z y M P R O = C) :
    codes (JTSupportedPathWhiskeredDiagram.labels W x z y M S u hs P R O) =
      JTSupportedPathChainLabels.toOriginal W z M S u hs ⋙ codes C :=
  (JTSupportedPathWhiskeredGraph.code_reindex W x z y M S u hs P R O).trans
    (congrArg (fun N ↦ JTSupportedPathChainLabels.toOriginal W z M S u hs ⋙ codes N) e)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels F j
private abbrev S := JTSharedInsertionCoarseMiddleSupport.supports F j
private abbrev u := JTSharedInsertionCoarseMiddleSupport.inclusion F j
private abbrev hs := JTSharedInsertionCoarseMiddleSupport.coefficient_onSupport F j
private abbrev P := JTSharedInsertionCoarseWhiskeredData.leftNative F j
private abbrev R := JTSharedInsertionCoarseWhiskeredData.rightNative F j
private abbrev O := JTSharedInsertionCoarseWhiskeredData.surroundings F j

/-- Both native padding edges remain even for a zero-width original chart. -/
theorem middle_positive (p : JTSharedInsertionChoices.Index F j) :
    0 < ((codes (M F j)).obj p).len :=
  padded_positive _

/-- All higher supported paths and both complete chain refinements. -/
abbrev Index := JTSupportedPathChainLabels.Index W (z j) (M F j) (S F j) (u F j) (hs F j)

/-- Forget the complete path and chain choices to the SAME insertion choices. -/
def toChoices :=
  JTSupportedPathChainLabels.toOriginal W (z j) (M F j) (S F j) (u F j) (hs F j)

/-- The full coefficient ordinal of each supported path chain. -/
abbrev ordinals :=
  JTSupportedPathChainLabels.ordinals W (z j) (M F j) (S F j) (u F j) (hs F j)

/-- The original shared coefficient coordinate, without choosing a section. -/
abbrev toOldCoefficient :=
  JTSupportedPathChainLabels.toOldCoefficient W (z j) (M F j) (S F j) (u F j) (hs F j)

/-- Keep both actual surrounding coefficients throughout the supported middle path. -/
abbrev family := JTSupportedPathWhiskeredDiagram.variableMiddleFamily W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)

/-- The actual entire supported path of decorated labels, in the original endpoints. -/
def labels := JTSupportedPathWhiskeredDiagram.labels W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)

/-- All native pieces and every native operator are the original coarse ones. -/
def codes_reindex := codesReindex W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseLabels.labels F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- The actual complete path projection is weak over precisely Shared.Index.
The result type is inferred from the existing full-cover theorem, retaining its
exact weak-equivalence conclusion and adding no premise. -/
def toChoices_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :=
  JTSupportedPathChainLabels.toOriginal_weak W (z j) (M F j) (S F j) (u F j) (hs F j)
    (JTSharedInsertionCoarseMiddleSupport.inclusion_mono F j) hW (middle_positive F j)

end
end DaggerModels.PartII.JTSharedInsertionCoarseSupportedLabels
