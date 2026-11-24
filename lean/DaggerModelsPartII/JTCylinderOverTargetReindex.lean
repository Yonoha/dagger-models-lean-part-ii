import DaggerModelsPartII.JTCylinderOverTarget

/-!
# Time reindexing of the whole endpoint-cylinder target comparison
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCylinderOverTargetReindex

open JTCylinderOverTarget JTTargetCommaPullback
open JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
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
variable (T : NecklaceCode) (m n : SimplexCategory) (j : m ⟶ n)
variable (h_m : (under T).obj m ⟶ (underDiagram W x y).obj i)
variable (h_n : (under T).obj n ⟶ (underDiagram W x y).obj i)
variable (d : T ⟶ Q.code)
variable (hr_m : h_m.right ≫ ((underCocone W x y).app i).right =
  augmentation T m ≫ d.map ≫ Q.map)
variable (hr_n : h_n.right ≫ ((underCocone W x y).app i).right =
  augmentation T n ≫ d.map ≫ Q.map)
variable (hj : (under T).map j ≫ h_n = h_m)

/-- The native target leg commutes with every simplex operator. -/
theorem native_reindex :
    (under T).map j ≫ JTCylinderOverTarget.native W x y Q T n d =
      JTCylinderOverTarget.native W x y Q T m d := by
  apply Under.UnderMorphism.ext
  change (value T).map j ≫ augmentation T n ≫ d.map =
    augmentation T m ≫ d.map
  rw [← Category.assoc, augmentation_parameter_natural]

include hj in
/-- Both pullback projections identify the restricted and original lifts. -/
theorem lift_reindex :
    (under T).map j ≫ JTCylinderOverTarget.lift W x y Q i T n h_n d hr_n =
      JTCylinderOverTarget.lift W x y Q i T m h_m d hr_m := by
  apply pullback.hom_ext (f := (underCocone W x y).app i)
    (g := targetMap W x y Q)
  · calc
      ((under T).map j ≫ JTCylinderOverTarget.lift W x y Q i T n h_n d hr_n) ≫
          fst W x y Q i =
        (under T).map j ≫
          (JTCylinderOverTarget.lift W x y Q i T n h_n d hr_n ≫ fst W x y Q i) :=
        Category.assoc _ _ _
      _ = (under T).map j ≫ h_n := by rw [JTCylinderOverTarget.lift_decorated]
      _ = h_m := hj
      _ = JTCylinderOverTarget.lift W x y Q i T m h_m d hr_m ≫ fst W x y Q i :=
        (JTCylinderOverTarget.lift_decorated W x y Q i T m h_m d hr_m).symm
  · calc
      ((under T).map j ≫ JTCylinderOverTarget.lift W x y Q i T n h_n d hr_n) ≫
          snd W x y Q i =
        (under T).map j ≫
          (JTCylinderOverTarget.lift W x y Q i T n h_n d hr_n ≫ snd W x y Q i) :=
        Category.assoc _ _ _
      _ = (under T).map j ≫ JTCylinderOverTarget.native W x y Q T n d := by
        rw [JTCylinderOverTarget.lift_native]
      _ = JTCylinderOverTarget.native W x y Q T m d := native_reindex W x y Q T m n j d
      _ = JTCylinderOverTarget.lift W x y Q i T m h_m d hr_m ≫ snd W x y Q i :=
        (JTCylinderOverTarget.lift_native W x y Q i T m h_m d hr_m).symm

include hj in
/-- The entire fixed-target comma functor is strict under time reindexing. -/
theorem functor_reindex :
    CostructuredArrow.map ((under T).map j) ⋙
      JTCylinderOverTarget.functor W x y Q i T n h_n d hr_n =
    JTCylinderOverTarget.functor W x y Q i T m h_m d hr_m := by
  have hc := congrArg (fun f ↦ f.toFunctor)
    ((BoundaryNecklaceComma.diagram).map_comp ((under T).map j)
      (JTCylinderOverTarget.lift W x y Q i T n h_n d hr_n))
  have hf : CostructuredArrow.map ((under T).map j) ⋙
      JTCylinderOverTarget.atBase W x y Q i T n h_n d hr_n =
      JTCylinderOverTarget.atBase W x y Q i T m h_m d hr_m := by
    calc
      _ = CostructuredArrow.map
          ((under T).map j ≫
            JTCylinderOverTarget.lift W x y Q i T n h_n d hr_n) := hc.symm
      _ = _ := congrArg CostructuredArrow.map
        (lift_reindex W x y Q i T m n j h_m h_n d hr_m hr_n hj)
  exact congrArg (fun F ↦ F ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (diagram W x y Q)) i ⋙
      (equivalence W x y Q).inverse) hf

end

end DaggerModels.PartII.JTCylinderOverTargetReindex
