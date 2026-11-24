import DaggerModelsPartII.JTSharedInsertionSeamNative

/-!
# All seam comparisons over the original source, before the map to Q

The source-level triangles are needed for the original-time parameter equations:
commuting only after the collapse into Q would not suffice. Each phase keeps the
same original source functor and both global endpoints. No raw equation is added.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionPhaseNative

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev seam := JTSharedInsertionNormalizedSeam.seamFamily F j
private abbrev original := JTSharedInsertionSeamNative.original F j

/-- The whole long-edge phase returns to the original source before its Q-collapse. -/
def longNative : codes (JTWhiskeredSeamDiagram.longFamily (seam F j)).labels ⟶
    original F j ⋙ codes L :=
  JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.longToCollapsed F j) ≫
    JTSharedInsertionSeamNative.collapsedNative F j

/-- The whole detour returns to that SAME original source through the triangle. -/
def detourNative : codes (JTWhiskeredSeamDiagram.detourFamily (seam F j)).labels ⟶
    original F j ⋙ codes L :=
  JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.detourToTriangle F j) ≫
    JTSharedInsertionSeamNative.wholeNative F j

/-- The detour comparison is compatible with the original source parameter input. -/
theorem detour_source_square :
    JTWhiskeredSeamTarget.nativeOf
        (JTSharedInsertionNormalizedSeam.detourToTriangle F j) ≫
      JTSharedInsertionSeamNative.wholeNative F j = detourNative F j := rfl

/-- The long-edge comparison commutes BEFORE postcomposition with F.collapse. -/
theorem long_source_square :
    JTWhiskeredSeamTarget.nativeOf
        (JTSharedInsertionNormalizedSeam.longToTriangle F j) ≫
      JTSharedInsertionSeamNative.wholeNative F j = longNative F j := by
  change JTWhiskeredSeamTarget.nativeOf
      (JTWhiskeredSeamDiagram.longToTriangle (seam F j)) ≫
    (JTWhiskeredSeamTarget.triangleToCollapsed (seam F j) ≫
      JTSharedInsertionSeamNative.collapsedNative F j) = _
  rw [← Category.assoc, JTWhiskeredSeamTarget.long_triangle_collapsed]
  rfl

/-- The identity-edge collapse retains the very same original source map. -/
theorem collapsed_source_square :
    JTWhiskeredSeamTarget.nativeOf
        (JTSharedInsertionNormalizedSeam.longToCollapsed F j) ≫
      JTSharedInsertionSeamNative.collapsedNative F j = longNative F j := rfl

end
end DaggerModels.PartII.JTSharedInsertionPhaseNative
