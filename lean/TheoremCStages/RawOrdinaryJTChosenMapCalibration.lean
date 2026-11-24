import RawOrdinaryJTEndpointCalibration
import OrdinarySegalOrderedMappingMaps
import DaggerModelsPartII.ChosenHomotopyFiberFunctor

/-!
# The literal raw JT chosen map is the standard ordinary ordered chosen map

This calibrates the unchanged raw transpose at the original projective-image
vertices. It makes no CSS weak-to-DK inference and asserts no weakness of the
raw map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.RawOrdinaryJTChosenMapCalibration

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingMaps (endpointMap endpoint_naturality point_naturality)
open ChosenHomotopyFiberComparison (chosenFiber)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F (W : Source) :
    RawOrdinaryJTQuillenTranspose.input W ⟶
      OrdinaryJTCurriedAdjunction.right.obj
        (JTRawFreeInnerComparison.rawTarget W).toSSet :=
  JTRealizationDiagonal.ordinaryCurry.map (JTRawOrdinaryAdjoint.gRawTilde W)

/-- The standard chosen ordered mapping-fiber action of an ordinary-space map. -/
def chosenMappingMap {U V : Space} (f : U ⟶ V)
    (x y : (U.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    chosenFiber (endpointArrow U) (endpointPoint U x y) ⟶
      chosenFiber (endpointArrow V)
        (endpointPoint V ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
          ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y)) :=
  ChosenHomotopyFiberFunctor.chosenMap (endpointArrow U) (endpointArrow V)
    (f.app (op ⦋1⦌)) (endpointMap f) (endpoint_naturality f)
    (endpointPoint U x y) _ (point_naturality f x y)

private theorem face_zero :
    JTXiEndpointCollapseBoundary.ordinaryEndpoint (0 : Fin 2) =
      SimplexCategory.δ (1 : Fin 2) := by
  ext j
  fin_cases j; rfl

private theorem face_one :
    JTXiEndpointCollapseBoundary.ordinaryEndpoint (1 : Fin 2) =
      SimplexCategory.δ (0 : Fin 2) := by
  ext j
  fin_cases j; rfl

private theorem source_endpoint (W : Source) :
    JTProjectiveOrderedFiberComparison.endpointArrow W =
      endpointArrow (RawOrdinaryJTQuillenTranspose.input W) := by
  change prod.lift
      ((RawOrdinaryJTQuillenTranspose.input W).map
        (JTXiEndpointCollapseBoundary.ordinaryEndpoint (0 : Fin 2)).op)
      ((RawOrdinaryJTQuillenTranspose.input W).map
        (JTXiEndpointCollapseBoundary.ordinaryEndpoint (1 : Fin 2)).op) =
    prod.lift
      ((RawOrdinaryJTQuillenTranspose.input W).map (SimplexCategory.δ (1 : Fin 2)).op)
      ((RawOrdinaryJTQuillenTranspose.input W).map (SimplexCategory.δ (0 : Fin 2)).op)
  rw [face_zero, face_one]

private theorem target_endpoint (W : Source) :
    JTRightAdjointOrderedFiber.ordinaryEndpointArrow
        (JTRawFreeInnerComparison.rawTarget W).toSSet =
      endpointArrow (OrdinaryJTCurriedAdjunction.right.obj
        (JTRawFreeInnerComparison.rawTarget W).toSSet) := by
  let V := OrdinaryJTCurriedAdjunction.right.obj
    (JTRawFreeInnerComparison.rawTarget W).toSSet
  change prod.lift (V.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint (0 : Fin 2)).op)
      (V.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint (1 : Fin 2)).op) =
    prod.lift (V.map (SimplexCategory.δ (1 : Fin 2)).op)
      (V.map (SimplexCategory.δ (0 : Fin 2)).op)
  rw [face_zero, face_one]

private theorem source_point (W : Source)
    (u v : ((RawOrdinaryJTQuillenTranspose.input W).obj (op ⦋0⦌)).obj
      (op ⦋0⦌)) :
    JTProjectiveOrderedFiberComparison.point W u v =
      endpointPoint (RawOrdinaryJTQuillenTranspose.input W) u v := rfl

private theorem raw_base (W : Source) :
    JTRawOrdinaryAdjoint.gRawBase W = endpointMap (F W) := rfl

private theorem target_point (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    JTRightAdjointOrderedFiber.ordinaryEndpointPoint
        (JTRawFreeInnerComparison.rawTarget W)
        ((JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertices W x y).1)
        ((JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertices W x y).2) =
      endpointPoint (OrdinaryJTCurriedAdjunction.right.obj
        (JTRawFreeInnerComparison.rawTarget W).toSSet)
        (((F W).app (op ⦋0⦌)).app (op ⦋0⦌)
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).1)
        (((F W).app (op ⦋0⦌)).app (op ⦋0⦌)
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) := by
  let u := (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
  let v := (JTProjectiveOrderedFiberComparison.targetVertices W x y).2
  calc
    _ = JTProjectiveOrderedFiberComparison.point W u v ≫
          JTRawOrdinaryAdjoint.gRawBase W :=
        (JTRawOrdinaryAdjoint.rawPoint_square_at_p W x y).symm
    _ = endpointPoint (RawOrdinaryJTQuillenTranspose.input W) u v ≫
          endpointMap (F W) := by rw [source_point W u v, raw_base W]
    _ = _ := point_naturality (F W) u v

private theorem chosenMap_heq {X Y B D K : SSet.{0}}
    {p p' : X ⟶ B} {q q' : Y ⟶ D} {f f' : X ⟶ Y} {g g' : B ⟶ D}
    {h : p ≫ g = f ≫ q} {h' : p' ≫ g' = f' ≫ q'}
    {b b' : K ⟶ B} {d d' : K ⟶ D} {hb : b ≫ g = d} {hb' : b' ≫ g' = d'}
    (hp : p = p') (hq : q = q') (hf : f = f') (hg : g = g')
    (hpoint : b = b') (hd : d = d') :
    HEq (ChosenHomotopyFiberFunctor.chosenMap p q f g h b d hb)
      (ChosenHomotopyFiberFunctor.chosenMap p' q' f' g' h' b' d' hb') := by
  subst p'
  subst q'
  subst f'
  subst g'
  subst b'
  subst d'
  rfl

/-- The raw selected map and the standard curried chosen map have identical
point-set data at the two actual projective-image vertices. -/
theorem rawChosenFiberMapAtP_heq (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    HEq (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)
      (chosenMappingMap (F W)
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) := by
  exact chosenMap_heq (source_endpoint W) (target_endpoint W) rfl (raw_base W)
    (source_point W _ _) (target_point W x y)

private theorem weak_iff_of_heq {A B C D : SSet.{0}}
    {f : A ⟶ B} {g : C ⟶ D} (hA : A = C) (hB : B = D) (h : HEq f g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  cases hA
  cases hB
  rw [eq_of_heq h]

/-- Weakness of the unchanged raw chosen map is exactly weakness of the
standard ordinary chosen map of the same curried CSS morphism. -/
theorem rawChosenFiberMapAtP_weak_iff (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y) ↔
      WeakEquivalence (chosenMappingMap (F W)
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) := by
  have hSource :
      chosenFiber (JTProjectiveOrderedFiberComparison.endpointArrow W)
        (JTProjectiveOrderedFiberComparison.point W
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) =
        chosenFiber (endpointArrow (RawOrdinaryJTQuillenTranspose.input W))
          (endpointPoint (RawOrdinaryJTQuillenTranspose.input W)
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) := by
    simp only [source_endpoint W, source_point W]
  have hTarget :
      chosenFiber (JTRightAdjointOrderedFiber.ordinaryEndpointArrow
        (JTRawFreeInnerComparison.rawTarget W).toSSet)
        (JTRightAdjointOrderedFiber.ordinaryEndpointPoint
          (JTRawFreeInnerComparison.rawTarget W)
          ((JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
            (JTGtildeOrderedFiberAction.targetVertices W x y).1)
          ((JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
            (JTGtildeOrderedFiberAction.targetVertices W x y).2)) =
        chosenFiber (endpointArrow (OrdinaryJTCurriedAdjunction.right.obj
          (JTRawFreeInnerComparison.rawTarget W).toSSet))
          (endpointPoint (OrdinaryJTCurriedAdjunction.right.obj
            (JTRawFreeInnerComparison.rawTarget W).toSSet)
            (((F W).app (op ⦋0⦌)).app (op ⦋0⦌)
              (JTProjectiveOrderedFiberComparison.targetVertices W x y).1)
            (((F W).app (op ⦋0⦌)).app (op ⦋0⦌)
              (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)) := by
    simp only [target_endpoint W, target_point W x y]
  exact weak_iff_of_heq hSource hTarget (rawChosenFiberMapAtP_heq W x y)

#print axioms rawChosenFiberMapAtP_heq
#print axioms rawChosenFiberMapAtP_weak_iff

end

end DaggerModels.PartII.RawOrdinaryJTChosenMapCalibration
