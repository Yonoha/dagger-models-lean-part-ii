import DaggerModelsPartII.JTTargetCommaPullback
import DaggerModelsPartII.NecklaceCylinderAugmentation

/-!
# A whole endpoint cylinder over a fixed decorated target
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCylinderOverTarget

open JTTargetCommaPullback JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (i : DecoratedNecklaceHomDiagram.Index W x y)
variable (T : NecklaceCode) (n : SimplexCategory)
variable (h : (under T).obj n ⟶ (underDiagram W x y).obj i)
variable (d : T ⟶ Q.code)
variable (hr : h.right ≫ ((underCocone W x y).app i).right =
  augmentation T n ≫ d.map ≫ Q.map)

/-- The augmentation followed by the original native code map, under both endpoints. -/
def native : (under T).obj n ⟶ necklaceUnder.obj Q.code :=
  Under.homMk (augmentation T n ≫ d.map) (by
    change (boundary T).app n ≫ augmentation T n ≫ d.map = endpointInclusion Q.code
    rw [← Category.assoc, augmentation_boundary, endpointInclusion_natural])

/-- Pair the decorated cylinder map with the original native target map. -/
def lift : (under T).obj n ⟶ (diagram W x y Q).obj i :=
  pullback.lift h (native W x y Q T n d) (by
    apply Under.UnderMorphism.ext
    exact hr)

theorem lift_decorated :
    lift W x y Q i T n h d hr ≫ fst W x y Q i = h :=
  pullback.lift_fst _ _ _

theorem lift_native :
    lift W x y Q i T n h d hr ≫ snd W x y Q i = native W x y Q T n d :=
  pullback.lift_snd _ _ _

/-- Postcompose each internal native necklace by the whole pullback lift. -/
def atBase :
    CostructuredArrow necklaceUnder ((under T).obj n) ⥤
      CostructuredArrow necklaceUnder ((diagram W x y Q).obj i) :=
  CostructuredArrow.map (lift W x y Q i T n h d hr)

/-- The resulting full comma functor has the original fixed target. -/
def functor :
    CostructuredArrow necklaceUnder ((under T).obj n) ⥤
      CostructuredArrow (toTarget W x y) Q :=
  atBase W x y Q i T n h d hr ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (diagram W x y Q)) i ⋙
      (equivalence W x y Q).inverse

/-- The explicit object built from the fixed-base pullback presentation. -/
def targetObject (P : CostructuredArrow necklaceUnder ((under T).obj n)) :
    CostructuredArrow (toTarget W x y) Q :=
  fromObj W x y Q
    ((Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (diagram W x y Q)) i).obj
      ((atBase W x y Q i T n h d hr).obj P))

theorem targetObject_code
    (P : CostructuredArrow necklaceUnder ((under T).obj n)) :
    (targetObject W x y Q i T n h d hr P).left.fiber.left = P.left := rfl

theorem targetObject_map
    (P : CostructuredArrow necklaceUnder ((under T).obj n)) :
    (targetObject W x y Q i T n h d hr P).left.fiber.hom.right =
      P.hom.right ≫ h.right := by
  change (P.hom ≫ lift W x y Q i T n h d hr ≫ fst W x y Q i).right = _
  rw [lift_decorated]
  rfl

theorem targetObject_native_map
    (P : CostructuredArrow necklaceUnder ((under T).obj n)) :
    (targetObject W x y Q i T n h d hr P).hom.hom.map =
      P.hom.right ≫ augmentation T n ≫ d.map := by
  change (P.hom ≫ lift W x y Q i T n h d hr ≫ snd W x y Q i).right = _
  rw [lift_native]
  rfl

private theorem pair_fromObj
    (R : JTTargetCommaPullback.Presentation W x y Q) :
    (toPullback W x y Q).obj (fromObj W x y Q R) = R := by
  have h : JTTargetCommaPullback.lift W x y Q (fromObj W x y Q R) = R.fiber.hom := by
    apply pullback.hom_ext (f := (underCocone W x y).app R.base)
      (g := targetMap W x y Q)
    · change JTTargetCommaPullback.lift W x y Q (fromObj W x y Q R) ≫
          fst W x y Q R.base = R.fiber.hom ≫ fst W x y Q R.base
      exact JTTargetCommaPullback.lift_fst W x y Q (fromObj W x y Q R)
    · change JTTargetCommaPullback.lift W x y Q (fromObj W x y Q R) ≫
          snd W x y Q R.base = R.fiber.hom ≫ snd W x y Q R.base
      exact (JTTargetCommaPullback.lift_snd W x y Q (fromObj W x y Q R)).trans
        (by apply Under.UnderMorphism.ext; rfl)
  exact congrArg (fun m ↦ ⟨R.base, CostructuredArrow.mk m⟩ :
    _ → JTTargetCommaPullback.Presentation W x y Q) h

private def inverseObjIsoFromObj
    (R : JTTargetCommaPullback.Presentation W x y Q) :
    (equivalence W x y Q).inverse.obj R ≅ fromObj W x y Q R :=
  ((equivalence W x y Q).inverse.mapIso
    (eqToIso (pair_fromObj W x y Q R).symm)).trans
      ((equivalence W x y Q).unitIso.app (fromObj W x y Q R)).symm

/-- The canonical inverse is isomorphic to the explicit unchanged-code target object. -/
def functor_obj_iso
    (P : CostructuredArrow necklaceUnder ((under T).obj n)) :
    (functor W x y Q i T n h d hr).obj P ≅
      targetObject W x y Q i T n h d hr P :=
  inverseObjIsoFromObj W x y Q _

end

end DaggerModels.PartII.JTCylinderOverTarget
