import DaggerModelsPartII.JTGraphMultiBeadIdentityLift

/-!
# Factoring an original presentation over the unchanged raw target
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphFactoredPresentation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphLiftTransport
open JTCommaGraphPredecessor (augmentationCode)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

abbrev TargetComma (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  CostructuredArrow (toTarget W x y) Q

abbrev Traversal (U : TargetComma Q) (T : NecklaceCode) :=
  BoundaryNecklaceComma.necklaceUnder.obj T ⟶ (underDiagram W x y).obj U.left.base

variable {U : TargetComma Q} {S T : NecklaceCode}

private def presentation (U : TargetComma Q) (v : Traversal U T) :
    Pres (W := W) (x := x) (y := y) :=
  ⟨U.left.base, CostructuredArrow.mk v⟩

/-- The raw evaluation factors on the same native quotient whenever the
whole reduced-cylinder traversal and the native map to the target both factor. -/
def object (U : TargetComma Q) (c : S ⟶ U.left.fiber.left) (g : S ⟶ T)
    [Epi g.map] (v : Traversal U T) (r : T ⟶ Q.code)
    (hv : g.map ≫ v.right = c.map ≫ U.left.fiber.hom.right)
    (hr : g ≫ r = c ≫ U.hom.hom) : TargetComma Q :=
  CostructuredArrow.mk (Y := presentation U v) (⟨r, by
    let d := ((underCocone W x y).app U.left.base).right
    change r.map ≫ Q.map = v.right ≫ d
    apply (cancel_epi g.map).mp
    have h : g.map ≫ r.map = c.map ≫ U.hom.hom.map :=
      congrArg (fun f : S ⟶ Q.code ↦ f.map) hr
    have hu : U.hom.hom.map ≫ Q.map = U.left.fiber.hom.right ≫ d := U.hom.w
    calc
      g.map ≫ r.map ≫ Q.map = (g.map ≫ r.map) ≫ Q.map :=
        (Category.assoc _ _ _).symm
      _ = c.map ≫ U.hom.hom.map ≫ Q.map := by rw [h, Category.assoc]
      _ = c.map ≫ U.left.fiber.hom.right ≫ d := congrArg (fun f ↦ c.map ≫ f) hu
      _ = (c.map ≫ U.left.fiber.hom.right) ≫ d := (Category.assoc _ _ _).symm
      _ = (g.map ≫ v.right) ≫ d := congrArg (fun f ↦ f ≫ d) hv.symm
      _ = g.map ≫ v.right ≫ d := Category.assoc _ _ _⟩)

variable (c : S ⟶ U.left.fiber.left) (g : S ⟶ T) [Epi g.map]
  (v : Traversal U T) (r : T ⟶ Q.code)
  (hv : g.map ≫ v.right = c.map ≫ U.left.fiber.hom.right)
  (hr : g ≫ r = c ≫ U.hom.hom)

theorem object_base : (object U c g v r hv hr).left.base = U.left.base := rfl

theorem object_code : (object U c g v r hv hr).left.fiber.left = T := rfl

theorem object_traversal : (object U c g v r hv hr).left.fiber.hom.right = v.right := rfl

theorem object_native_target : (object U c g v r hv hr).hom.hom = r := rfl

/-- The horizontal map of the original graph factors with the traversal. -/
theorem horizontal_factor :
    c ≫ augmentationCode U.left = g ≫ augmentationCode (object U c g v r hv hr).left := by
  apply NecklaceCode.Hom.ext
  let a := NecklaceCylinderAugmentation.augmentation (code U.left) (degree U.left)
  change c.map ≫ U.left.fiber.hom.right ≫ a = g.map ≫ v.right ≫ a
  calc
    _ = (c.map ≫ U.left.fiber.hom.right) ≫ a := (Category.assoc _ _ _).symm
    _ = (g.map ≫ v.right) ≫ a := congrArg (fun f ↦ f ≫ a) hv.symm
    _ = _ := Category.assoc _ _ _

end

end DaggerModels.PartII.JTGraphFactoredPresentation
