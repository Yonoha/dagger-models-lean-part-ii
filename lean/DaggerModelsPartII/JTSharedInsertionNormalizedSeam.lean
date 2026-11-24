import DaggerModelsPartII.JTSharedInsertionSeamSurroundings
import DaggerModelsPartII.JTSharedInsertionSeamTriangles
import DaggerModelsPartII.JTChosenSeamOldComparison
import DaggerModelsPartII.JTChosenSeamChainDiagram

/-!
# The actual insertion seam with the same outer correction labels

The complete ending/starting pair at the inserted cut is replaced through its
relative triangle and identity edge while retaining the actual corrections at
both outer cuts. The original global endpoints and every coefficient/choice
operator are preserved. Complete raw evaluation in the original Q is subsequent
work; these decorated-label comparisons do not assert it.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionNormalizedSeam

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev U := JTSharedInsertionChainSupport.diagram F j 1
private abbrev K := JTSharedInsertionChoices.ordinals F j
private abbrev incl := JTSharedInsertionChainSupport.inclusion F j 1
private abbrev f := JTSharedInsertionChainSupport.rows F j 1
private abbrev e := JTSharedInsertionIncidentEdges.ending F j 1
private abbrev s := JTSharedInsertionIncidentEdges.starting F j 1
private abbrev he := JTSharedInsertionIncidentEdges.ending_endpoints F j 1
private abbrev hs := JTSharedInsertionIncidentEdges.starting_endpoints F j 1
private abbrev hfU := JTSharedInsertionChainSupport.row_on_support F j 1
private abbrev heU := JTSharedInsertionIncidentEdges.ending_on_support F j 1
private abbrev hsU := JTSharedInsertionIncidentEdges.starting_on_support F j 1

private abbrev O := JTSharedInsertionSeamSurroundings.surroundings F j

/-- The actual full seam-triangle choice chain at this insertion. -/
abbrev Index := JTSharedInsertionSeamTriangles.Index F j

/-- The unchanged original object and operator throughout all four phases. -/
abbrev original : Index F j ⥤ A :=
  JTSharedInsertionSeamTriangles.toOriginal F j ⋙
    JTSharedInsertionChainSupport.originalBase F j

/-- The coefficient simplex of the ORIGINAL family at that same old object. -/
abbrev oldDegrees := original F j ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

/-- Both full-chain projections compose without choosing a parameter section. -/
def coefficientProjection : JTSharedInsertionSeamTriangles.ordinals F j ⟶ oldDegrees F j :=
  JTSharedInsertionSeamTriangles.toOld F j ≫
    Functor.whiskerLeft (JTSharedInsertionSeamTriangles.toOriginal F j)
      (JTSharedInsertionChoices.toOriginal F j)

/-- This composite retains every original coefficient vertex. -/
theorem coefficientProjection_surjective (p : Index F j) :
    Function.Surjective ((coefficientProjection F j).app p).toOrderHom := by
  have hnew : Function.Surjective
      ((JTSharedInsertionSeamTriangles.toOld F j).app p).toOrderHom :=
    TimePrismChainDiagram.coeffProjection_surjective _ _ p
  exact (JTSharedInsertionChoices.toOriginal_surjective F j
    ((JTSharedInsertionSeamTriangles.toOriginal F j).obj p)).comp hnew

/-- All four phases have the SAME actual outer corrected coefficients. -/
abbrev seamFamily := JTChosenSeamChainDiagram.seamFamily W (z j) (U F j) (K F j)
  (incl F j) (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
  (O F j)

/-- The full ending/starting detour maps naturally into the actual chosen triangle. -/
def detourToTriangle := JTChosenSeamChainDiagram.detourToTriangle W (z j)
  (U F j) (K F j) (incl F j) (f F j) (e F j) (s F j) (he F j) (hs F j)
  (hfU F j) (heU F j) (hsU F j) (O F j)

/-- The identity long edge maps naturally into the SAME chosen triangle. -/
def longToTriangle := JTChosenSeamChainDiagram.longToTriangle W (z j)
  (U F j) (K F j) (incl F j) (f F j) (e F j) (s F j) (he F j) (hs F j)
  (hfU F j) (heU F j) (hsU F j) (O F j)

/-- The identity long edge collapses naturally at the original varying row. -/
def longToCollapsed := JTChosenSeamChainDiagram.longToCollapsed W (z j)
  (U F j) (K F j) (incl F j) (f F j) (e F j) (s F j) (he F j) (hs F j)
  (hfU F j) (heU F j) (hsU F j) (O F j)

/-- The old split label retains both outside correction pairs and the row at b. -/
abbrev oldFamily := JTChosenSeamOldComparison.oldFamily W (K F j) (f F j) (O F j)

/-- All chosen collapsed labels compare to those EXACT original-degree split labels. -/
def collapsedToOld := JTChosenSeamOldComparison.comparison W (z j)
  (U F j) (K F j) (incl F j) (f F j) (e F j) (s F j) (he F j) (hs F j)
  (hfU F j) (heU F j) (hsU F j) (O F j)

end
end DaggerModels.PartII.JTSharedInsertionNormalizedSeam
