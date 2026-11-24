import DaggerModelsPartII.JTDecoratedIntervalDiagram
import DaggerModelsPartII.JTMarkedSemisimplicialSpanEvaluation

/-! Full decorated traversals and their interval restrictions on the exact evaluation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTMarkedSpanIntervalTraversal

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTDecoratedIntervalDiagram
open DecoratedCylinderNecklacePresentation (toTarget projection underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable {I : Type} [SmallCategory I] (E : I ⥤ TargetComma Q)

abbrev native := E ⋙ JTTargetJointMarks.nativeOver W x y Q
abbrev labels := E ⋙ CostructuredArrow.proj (toTarget W x y) Q ⋙ projection W x y

private abbrev decorated := labels Q E ⋙ JTDecoratedCylinderOverMapping.rawTarget W x y
private abbrev nativeWhole := native Q E ⋙ JTTargetIntervalOverMapping.whole Q.code

/-- The complete original decorative traversal is natural over the raw realization. -/
def rawTraversal : nativeWhole Q E ⋙ Over.map Q.map ⟶ decorated Q E where
  app p := Over.homMk (E.obj p).left.fiber.hom.right (by
    change (E.obj p).left.fiber.hom.right ≫
      ((underCocone W x y).app (E.obj p).left.base).right = (E.obj p).hom.hom.map ≫ Q.map
    exact (NecklacesOver.Hom.w (E.obj p).hom).symm)
  naturality {p p'} f := by
    apply Over.OverMorphism.ext
    let g := E.map f
    have h := (BoundaryNecklaceComma.evaluation (underDiagram W x y)).naturality g.left
    change BoundaryNecklaceComma.necklaceUnder.map g.left.fiber.left ≫
      (E.obj p').left.fiber.hom = (E.obj p).left.fiber.hom ≫
        (underDiagram W x y).map g.left.base at h
    exact congrArg (fun k ↦ k.right) h

variable (K : SimplexCategory ⥤ SSet.{0}) (time : I ⥤ SimplexCategory)

/-- Regard the exact original traversal as constant in the added time variable. -/
def traversal : wholeRaw K time Q (native Q E) ⟶ decorated Q E :=
  forgetParameter Q.map K time (nativeWhole Q E) ≫ rawTraversal Q E

variable (j : Joint Q.code)

/-- Restrict the original traversal to the entire left inverse-image interval. -/
def leftTraversal : leftRaw K time Q (native Q E) j ⟶ decorated Q E :=
  leftInclusion K time Q (native Q E) j ≫ traversal Q E K time

/-- Restrict the original traversal to the entire right inverse-image interval. -/
def rightTraversal : rightRaw K time Q (native Q E) j ⟶ decorated Q E :=
  rightInclusion K time Q (native Q E) j ≫ traversal Q E K time

/-- The exact left and right traversals agree on the full common interval,
including all source beads collapsed to the joint. -/
theorem agree_on_overlap :
    overlapLeft K time Q (native Q E) j ≫ leftTraversal Q E K time j =
      overlapRight K time Q (native Q E) j ≫ rightTraversal Q E K time j := by
  change _ ≫ _ ≫ traversal Q E K time = _ ≫ _ ≫ traversal Q E K time
  rw [← Category.assoc, ← Category.assoc, (interval_isPushout K time Q (native Q E) j).w]

/-- Gluing the restrictions recovers the entire exact traversal. -/
theorem glue_traversal :
    glue K time Q (native Q E) j (labels Q E) (leftTraversal Q E K time j)
        (rightTraversal Q E K time j) (agree_on_overlap Q E K time j) =
      traversal Q E K time :=
  (interval_isPushout K time Q (native Q E) j).hom_ext
    (glue_left K time Q (native Q E) j (labels Q E) _ _ _)
    (glue_right K time Q (native Q E) j (labels Q E) _ _ _)

variable (A : (nerve (TargetComma Q)).Subcomplex)

/-- The exact evaluated marked diagrams are instances of the full traversal. -/
abbrev markedTraversal (K : SimplexCategory ⥤ SSet.{0})
    (time : JTMarkedSemisimplicialSpanEvaluation.Marked Q A ⥤ SimplexCategory) :=
  traversal Q (JTMarkedSemisimplicialSpanEvaluation.markedEvaluation Q A) K time

end
end DaggerModels.PartII.JTMarkedSpanIntervalTraversal
