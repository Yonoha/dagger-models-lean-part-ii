import DaggerModelsPartII.JTEndpointNormalizationLifts
import DaggerModelsPartII.TwoBeadEndpointLabel
import DaggerModelsPartII.TwoBeadCylinderTraversal
import DaggerModelsPartII.DecoratedCylinderNecklacePresentation

/-!
# An actual normalized two-bead label and its internal necklace presentation

The specified original groupoid-parameter path is lifted through the original
endpoint arrow, restricted by the actual simplex unit, and glued as a whole
ordered label. The full three-bead cylinder traversal gives an actual object
of the retained presentation category. Agreement with a prescribed raw edge
after collapsing the outer beads is a separate, unproved target-map equation.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.NormalizedTwoBeadPresentation

open JTProjectiveOrderedFiberComparison
open JTEndpointNormalizationLifts
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌

variable {W : Source} {z : J ⟶ row W ⦋0⦌}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

/-- The actual normalized WHOLE degree-one label at the original fixed boundary. -/
def orderedLabel (d : Families W ⦋1⦌ 0 1 z x y) :
    ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W (boundaryPoint W x y)).obj
      (op TwoBeadCylinderTraversal.twoBead)).obj (op ⦋1⦌) :=
  TwoBeadEndpointLabel.orderedWedgePointFromRow W x y
    (leftSimplexFamily d) (rightSimplexFamily d)
    (by
      have hl := congrArg (fun q ↦ q ≫ prod.snd) (leftSimplex_boundary d)
      have hr := congrArg (fun q ↦ q ≫ prod.fst) (rightSimplex_boundary d)
      simp only [Category.assoc, endpointArrow, prod.lift_snd] at hl
      simp only [Category.assoc, endpointArrow, prod.lift_fst] at hr
      exact hl.trans hr.symm)
    (by
      have h := congrArg (fun q ↦ q ≫ prod.fst) (leftSimplex_boundary d)
      simpa only [Category.assoc, endpointArrow, prod.lift_fst] using h)
    (by
      have h := congrArg (fun q ↦ q ≫ prod.snd) (rightSimplex_boundary d)
      simpa only [Category.assoc, endpointArrow, prod.lift_snd] using h)

/-- The SAME accepted decorated label index object, without replacing its label. -/
def decoratedObject (d : Families W ⦋1⦌ 0 1 z x y) :
    DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) TwoBeadCylinderTraversal.twoBead
    ⦋1⦌ (orderedLabel d)

private theorem traversal_boundary :
    JTNecklaceEndpointCylinder.endpointInclusion TwoBeadCylinderTraversal.threeBead ≫
        TwoBeadCylinderTraversal.cylinderTraversal =
      (JTNecklaceEndpointCylinder.boundary TwoBeadCylinderTraversal.twoBead).app ⦋1⦌ := by
  apply SSet.boundary₁.hom_ext
  · rw [← Category.assoc]
    change (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc
      TwoBeadCylinderTraversal.threeBead.first TwoBeadCylinderTraversal.threeBead.last) ≫
        TwoBeadCylinderTraversal.cylinderTraversal = _
    rw [SSet.boundary₁.ι₀_desc]
    exact TwoBeadCylinderTraversal.cylinderTraversal_first_point
  · rw [← Category.assoc]
    change (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc
      TwoBeadCylinderTraversal.threeBead.first TwoBeadCylinderTraversal.threeBead.last) ≫
        TwoBeadCylinderTraversal.cylinderTraversal = _
    rw [SSet.boundary₁.ι₁_desc]
    exact TwoBeadCylinderTraversal.cylinderTraversal_last_point

/-- The full internal necklace over the ACTUAL selected reduced cylinder. -/
def presentationObject (d : Families W ⦋1⦌ 0 1 z x y) :
    DecoratedCylinderNecklacePresentation.Presentation W x y where
  base := decoratedObject d
  fiber := CostructuredArrow.mk (Y := TwoBeadCylinderTraversal.threeBead)
    (Under.homMk TwoBeadCylinderTraversal.cylinderTraversal traversal_boundary)

/-- The target is the SAME three-bead native necklace, at the SAME raw endpoints. -/
theorem target_code (d : Families W ⦋1⦌ 0 1 z x y) :
    ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
      (presentationObject d)).code = TwoBeadCylinderTraversal.threeBead := rfl

/-- The target map is the COMPLETE actual traversal followed by the SAME descended label. -/
theorem target_map (d : Families W ⦋1⦌ 0 1 z x y) :
    ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
        (presentationObject d)).map =
      TwoBeadCylinderTraversal.cylinderTraversal ≫
        JTNecklaceEndpointCylinder.descend W x y TwoBeadCylinderTraversal.twoBead
          ⦋1⦌ (orderedLabel d) := rfl

/-- Construct this actual presentation from the retained original fibrancy
and specified path equations. No arbitrary raw edge is substituted for z. -/
def chosenPresentation (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (z : J ⟶ row W ⦋0⦌) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ z = vertexPoint W x)
    (hy : JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ z = vertexPoint W y) :
    DecoratedCylinderNecklacePresentation.Presentation W x y :=
  presentationObject (normalizedFamilies W hW ⦋1⦌ 0 1 z x y hx hy)

end

end DaggerModels.PartII.NormalizedTwoBeadPresentation
