import DaggerModelsPartII.JTInsertionMiddleChartVertex
import DaggerModelsPartII.JTSharedInsertionSeamTriangles

/-!
# The actual shared triangle is stationary on the entire coarse chart support

Pull back the WHOLE coarse chart timed face along the literal composite of the
triangle-chain and shared-chain original-coefficient projections. Actual chart
containment puts this full preimage inside the triangle's full incident support.
The complete row-two triangle and all its boundary edges are therefore stationary
on that full coarse-chart support. No raw map, Family, target Q or fibrancy
hypothesis is added or replaced.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSharedInsertionChartTriangleSupport

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem constant_of_le {X Y : SSet.{0}} {U V : X.Subcomplex}
    (hUV : U ≤ V) (f : X ⟶ Y) (c : (Δ[0] : SSet.{0}) ⟶ Y)
    (h : V.ι ≫ f = term V.toSSet ≫ c) : U.ι ≫ f = term U.toSSet ≫ c := by
  let i := SSet.Subcomplex.homOfLE hUV
  calc
    U.ι ≫ f = i ≫ (V.ι ≫ f) := by rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]
    _ = i ≫ (term V.toSSet ≫ c) := congrArg (fun g ↦ i ≫ g) h
    _ = term U.toSSet ≫ c := by
      rw [← Category.assoc]
      congr 1

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- The actual full triangle-filler chain, with every original and choice operator retained. -/
abbrev Index := JTSharedInsertionSeamTriangles.Index F j

/-- Its original insertion data, including the given enclosing coarse chart. -/
abbrev toInsertion : Index F j ⥤ JTJointSubdivisionInsertion.Index F j :=
  JTSharedInsertionSeamTriangles.toOriginal F j ⋙ JTSharedInsertionChoices.base F j ⋙
    JTSharedInsertionChoices.projection F j

/-- The unchanged original coefficient degree of that actual insertion. -/
abbrev oldDegrees := toInsertion F j ⋙ JTJointSubdivisionInsertion.base F j ⋙
  JTJointRelativeGraphFamily.coefficient (L := L)

/-- The LITERAL composite projection from the full triangle chain to that original coefficient. -/
def toCoefficient : JTSharedInsertionSeamTriangles.ordinals F j ⟶ oldDegrees F j :=
  JTSharedInsertionSeamTriangles.toOld F j ≫
    Functor.whiskerLeft (JTSharedInsertionSeamTriangles.toOriginal F j)
      (JTSharedInsertionChoices.toOriginal F j)

/-- The entire original timed coarse-chart face, not merely its vertex support. -/
def chartFace (p : Index F j) : (std.obj ((oldDegrees F j).obj p)).Subcomplex :=
  SSet.Subcomplex.range (std.map (JTJointSubdivisionVertexSupport.beadInclusion F j
    ((toInsertion F j).obj p).1))

/-- Full preimage of that genuine chart face in the final triangle-chain simplex. -/
def fullChartSupport (p : Index F j) :
    (std.obj ((JTSharedInsertionSeamTriangles.ordinals F j).obj p)).Subcomplex :=
  (chartFace F j p).preimage (std.map ((toCoefficient F j).app p))

/-- Actual coarse-chart containment survives BOTH full original-coefficient projections. -/
theorem fullChartSupport_le_fullSupport (p : Index F j) :
    fullChartSupport F j p ≤ JTSharedInsertionSeamTriangles.fullSupport F j p := by
  intro n x hx
  have h := JTInsertionMiddleChartVertex.coarse_face_le_support F j ((toInsertion F j).obj p)
  apply h n
  exact hx

/-- The full coarse-chart support includes canonically in the actual full triangle support. -/
def toFullSupport (p : Index F j) :
    (fullChartSupport F j p).toSSet ⟶
      (JTSharedInsertionSeamTriangles.fullSupport F j p).toSSet :=
  SSet.Subcomplex.homOfLE (fullChartSupport_le_fullSupport F j p)

/-- This comparison is the literal inclusion into the SAME final chain simplex. -/
theorem toFullSupport_fac (p : Index F j) :
    toFullSupport F j p ≫ (JTSharedInsertionSeamTriangles.fullSupport F j p).ι =
      (fullChartSupport F j p).ι := rfl

/-- The ENTIRE actual triangle is the constant identity triangle on the whole chart preimage. -/
theorem triangle_on_fullChartSupport (p : Index F j) :
    (fullChartSupport F j p).ι ≫ (JTSharedInsertionSeamTriangles.triangle F j).app p =
      term (fullChartSupport F j p).toSSet ≫ vertexPoint W (z j) ≫
        JTRelativeSeamTriangle.identityTriangle W :=
  constant_of_le (fullChartSupport_le_fullSupport F j p)
    ((JTSharedInsertionSeamTriangles.triangle F j).app p)
    (vertexPoint W (z j) ≫ JTRelativeSeamTriangle.identityTriangle W)
    (JTSharedInsertionSeamTriangles.triangle_on_fullSupport F j p)

/-- All three actual boundary edges are stationary on the SAME full coarse-chart support. -/
theorem triangle_edge_on_fullChartSupport (p : Index F j) (i : Fin 3) :
    (fullChartSupport F j p).ι ≫
        ((JTSharedInsertionSeamTriangles.triangle F j).app p ≫
          JTRelativeSeamTriangle.rowEdge W i) =
      term (fullChartSupport F j p).toSSet ≫ vertexPoint W (z j) ≫
        JTEndpointNormalizationLifts.identityFamily W := by
  rw [← Category.assoc, triangle_on_fullChartSupport, Category.assoc, Category.assoc,
    JTRelativeSeamTriangle.identityTriangle_edge]

end
end DaggerModels.PartII.JTSharedInsertionChartTriangleSupport
