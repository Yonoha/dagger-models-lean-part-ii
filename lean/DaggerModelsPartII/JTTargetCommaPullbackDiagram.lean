import DaggerModelsPartII.DecoratedCylinderNecklacePresentation
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Over

/-!
# Pullbacks of the actual decorated cylinders over a fixed native target

The pullbacks are taken under the original ordered boundary. Each of their
two projections retains an entire endpoint-preserving simplicial map.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetCommaPullback

open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open BoundaryNecklaceComma (necklaceUnder fiberDiagram sourceCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev B := JTXiEndpointCollapse.boundary

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

local notation "D" => underDiagram W x y
local notation "ρ" => underCocone W x y
local notation "C" => CostructuredArrow (toTarget W x y) Q
local notation "I" => DecoratedNecklaceHomDiagram.Index W x y

/-- The original target map, as a morphism under both specified endpoints. -/
def targetMap : necklaceUnder.obj Q.code ⟶
    JTConeMappingPresentation.targetUnder (Raw W) (rawVertex W x) (rawVertex W y) :=
  Under.homMk Q.map (by
    change JTNecklaceEndpointCylinder.endpointInclusion Q.code ≫ Q.map =
      JTConeMappingPresentation.orderedBoundary (Raw W) (rawVertex W x) (rawVertex W y)
    rw [JTNecklaceEndpointCylinder.endpointInclusion,
      JTGeneralOrderedFiberWeak.orderedBoundary_natural, Q.first, Q.last])

/-- The actual pullbacks of descended cylinders along the fixed native map. -/
def diagram : I ⥤ Under B :=
  Over.lift D ρ ⋙ Over.pullback (targetMap W x y Q) ⋙
    Over.forget (necklaceUnder.obj Q.code)

local notation "E" => diagram W x y Q
local notation "q" => targetMap W x y Q

/-- The cylinder projection of the pullback. -/
def fst (i : I) : (E).obj i ⟶ (D).obj i := pullback.fst ((ρ).app i) q

/-- The projection to the same fixed native target code. -/
def snd (i : I) : (E).obj i ⟶ necklaceUnder.obj Q.code := pullback.snd ((ρ).app i) q

theorem condition (i : I) : fst W x y Q i ≫ (ρ).app i = snd W x y Q i ≫ q :=
  pullback.condition

@[reassoc]
theorem map_fst {i j : I} (f : i ⟶ j) :
    (E).map f ≫ fst W x y Q j = fst W x y Q i ≫ (D).map f :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd {i j : I} (f : i ⟶ j) :
    (E).map f ≫ snd W x y Q j = snd W x y Q i :=
  pullback.lift_snd _ _ _

private theorem over_target (P : C) :
    P.left.fiber.hom ≫ (ρ).app P.left.base = necklaceUnder.map P.hom.hom ≫ q := by
  apply Under.UnderMorphism.ext
  exact P.hom.w.symm

/-- Pair the original internal map with its actual comparison to the target. -/
def lift (P : C) : necklaceUnder.obj P.left.fiber.left ⟶ (E).obj P.left.base :=
  pullback.lift P.left.fiber.hom (necklaceUnder.map P.hom.hom) (over_target W x y Q P)

@[reassoc]
theorem lift_fst (P : C) : lift W x y Q P ≫ fst W x y Q P.left.base = P.left.fiber.hom :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem lift_snd (P : C) :
    lift W x y Q P ≫ snd W x y Q P.left.base = necklaceUnder.map P.hom.hom :=
  pullback.lift_snd _ _ _

/-- Pullback comparison respects the actual native arrow and its decorated operator. -/
theorem lift_naturality {P P' : C} (f : P ⟶ P') :
    necklaceUnder.map f.left.fiber.left ≫ lift W x y Q P' =
      lift W x y Q P ≫ (E).map f.left.base := by
  apply pullback.hom_ext (f := (ρ).app P'.left.base) (g := q)
  · change (_ ≫ _) ≫ fst W x y Q P'.left.base = (_ ≫ _) ≫ fst W x y Q P'.left.base
    simp only [Category.assoc, lift_fst, map_fst, lift_fst_assoc]
    exact CostructuredArrow.w f.left.fiber
  · change (_ ≫ _) ≫ snd W x y Q P'.left.base = (_ ≫ _) ≫ snd W x y Q P'.left.base
    simp only [Category.assoc, lift_snd, map_snd, ← necklaceUnder.map_comp]
    exact congrArg (fun g : (toTarget W x y).obj P.left ⟶ Q ↦ necklaceUnder.map g.hom)
      (CostructuredArrow.w f)

end

end DaggerModels.PartII.JTTargetCommaPullback
