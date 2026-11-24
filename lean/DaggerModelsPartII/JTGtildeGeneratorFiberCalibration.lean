import DaggerModelsPartII.JTGtildeOrderedFiberAction
import DaggerModelsPartII.JTCEOrdinaryFiber
import DaggerModelsPartII.JTRealizationGenerators

/-!
# Chosen ordinary vertices as actual coend generators

The two ordered vertices selected from the literal degree-(0,0) source row
are represented by the actual zero-parameter coend generator in the original
ordinary realization. Their images under the chosen free-inner map are
exactly the target vertices already used by the literal `gTilde` chosen-fiber
action. This is a point-set calibration, with no weakness assertion.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTGtildeGeneratorFiberCalibration

open JTGtildeOrderedFiberAction JTStrictificationMaps
open JTStrictificationCoefficients OrdinaryJTRealization

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := chosenOrdinaryInput W
private abbrev R (W : Source) : SSet.{0} := realization.obj (Input W)

/-- The literal degree-(0,0) source coefficient at the two-index point. -/
def zeroCoefficient (W : Source)
    (x : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (Input W).obj (op (⦋0⦌, ⦋0⦌)) := x

/-- The actual coend generator's zero vertex, using the fixed terminal
section of the groupoid parameter. No representative is chosen by a
non-natural surjectivity argument. -/
def zeroGeneratorVertex (W : Source)
    (x : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (R W).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv
    (zeroTensorVertex ≫
      JTRealizationGenerators.generator (Input W) (⦋0⦌, ⦋0⦌)
        (zeroCoefficient W x))

/-- The two original source vertices in the actual ordinary realization. -/
def zeroGeneratorVertices (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (R W).obj (op ⦋0⦌) × (R W).obj (op ⦋0⦌) :=
  (zeroGeneratorVertex W x, zeroGeneratorVertex W y)

/-- The chosen free-inner map sends the actual zero generator to the same
vertex extracted from the original `gTilde` row. -/
theorem chosenG_zeroGeneratorVertex (W : Source)
    (x : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (DaggerSSet.forget.map (chosenG W)).app (op ⦋0⦌)
      (zeroGeneratorVertex W x) =
        targetVertex W ((gRow W ⦋0⦌).app (op ⦋0⦌) x) := by
  have hg := gTilde_generator W (⦋0⦌, ⦋0⦌) (zeroCoefficient W x)
  change (gRow W ⦋0⦌).app (op ⦋0⦌) x =
    ULift.up
      (JTRealizationGenerators.generator (Input W) (⦋0⦌, ⦋0⦌)
        (zeroCoefficient W x) ≫ DaggerSSet.forget.map (chosenG W)) at hg
  simp only [zeroGeneratorVertex, targetVertex, hg,
    SSet.yonedaEquiv_comp]
  rfl

/-- Both images retain the specified order of the source pair. -/
theorem chosenG_zeroGeneratorVertices (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    ((DaggerSSet.forget.map (chosenG W)).app (op ⦋0⦌)
        (zeroGeneratorVertices W x y).1,
      (DaggerSSet.forget.map (chosenG W)).app (op ⦋0⦌)
        (zeroGeneratorVertices W x y).2) = targetVertices W x y := by
  apply Prod.ext
  · exact chosenG_zeroGeneratorVertex W x
  · exact chosenG_zeroGeneratorVertex W y

/-- The actual strict ordered-fiber action of the literal `gTilde` endpoint
square, before replacing either arrow by a fibration. -/
def strictFiberMap (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    pullback (sourceEndpointArrow W) (sourcePoint W x y) ⟶
      JTRightAdjointOrderedFiber.ordinaryOrderedFiber (chosenT W)
        (targetVertices W x y).1 (targetVertices W x y).2 :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    (sourceEndpointArrow W)
    (JTRightAdjointOrderedFiber.ordinaryEndpointArrow (chosenT W).toSSet)
    (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
    (sourcePoint W x y)
    (JTRightAdjointOrderedFiber.ordinaryEndpointPoint (chosenT W)
      (targetVertices W x y).1 (targetVertices W x y).2)
    (imagePoint_eq_ordinaryEndpointPoint W x y)

/-- The source simplex carried by the literal total projection of the
strict ordered fiber, with both original indices retained. -/
def oneCoefficient (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (sourceEndpointArrow W) (sourcePoint W x y)).obj (op k)) :
    (Input W).obj (op (⦋1⦌, k)) :=
  ((pullback.fst (sourceEndpointArrow W) (sourcePoint W x y)).app (op k)) z

/-- The actual CE interval leg of the strict-fiber action is the one-edge
coend generator followed by the chosen free-inner map. The ordered boundary
is inherited from the original strict-fiber point. -/
theorem strictFiberCE_interval (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (sourceEndpointArrow W) (sourcePoint W x y)).obj (op k)) :
    let u := (targetVertices W x y).1
    let v := (targetVertices W x y).2
    let f := ((JTCEOrdinaryFiber.originalFiberCEIso (chosenT W) u v).hom.app
      (op k)) ((strictFiberMap W x y).app (op k) z)
    JTXiEndpointCollapse.CE_interval.app k ≫ f.right =
      JTRealizationGenerators.generator (Input W) (⦋1⦌, k)
        (oneCoefficient W x y k z) ≫
          DaggerSSet.forget.map (chosenG W) := by
  dsimp only
  let u := (targetVertices W x y).1
  let v := (targetVertices W x y).2
  let z' := (strictFiberMap W x y).app (op k) z
  let f := ((JTCEOrdinaryFiber.originalFiberCEIso (chosenT W) u v).hom.app
    (op k)) z'
  have hce := JTCEOrdinaryFiber.ceSpanIso_hom_val (chosenT W) u v k f
  have hcollapse :
      ((JTCEOrdinaryFiber.ceSpanIso (chosenT W) u v).hom.app (op k) f).val =
      ((JTRightAdjointOrderedFiber.ordinaryOrderedFiberIso (chosenT W) u v).hom.app
        (op k) z').val := by
    let e := JTCEOrdinaryFiber.ceSpanIso (chosenT W) u v
    let d := JTRightAdjointOrderedFiber.ordinaryOrderedFiberIso (chosenT W) u v
    change (e.hom.app (op k) (e.inv.app (op k) (d.hom.app (op k) z'))).val =
      (d.hom.app (op k) z').val
    have hc := congrFun (Iso.inv_hom_id_app e (op k))
      (d.hom.app (op k) z')
    exact congrArg Subtype.val hc
  have hrow := JTRightAdjointOrderedFiber.ordinaryOrderedFiberIso_hom_val
    (chosenT W) u v k z'
  have hfst := DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst
    (sourceEndpointArrow W)
    (JTRightAdjointOrderedFiber.ordinaryEndpointArrow (chosenT W).toSSet)
    (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
    (sourcePoint W x y)
    (JTRightAdjointOrderedFiber.ordinaryEndpointPoint (chosenT W) u v)
    (imagePoint_eq_ordinaryEndpointPoint W x y)
  have hvalue := congrFun (NatTrans.congr_app hfst (op k)) z
  have hgen := gTilde_generator W (⦋1⦌, k) (oneCoefficient W x y k z)
  calc
    JTXiEndpointCollapse.CE_interval.app k ≫ f.right =
        ((JTCEOrdinaryFiber.ceSpanIso (chosenT W) u v).hom.app (op k) f).val :=
          hce.symm
    _ = ((JTRightAdjointOrderedFiber.ordinaryOrderedFiberIso
          (chosenT W) u v).hom.app (op k) z').val := hcollapse
    _ = ((pullback.fst
          (JTRightAdjointOrderedFiber.ordinaryEndpointArrow (chosenT W).toSSet)
          (JTRightAdjointOrderedFiber.ordinaryEndpointPoint (chosenT W) u v)).app
            (op k) z').down := hrow
    _ = ((gRow W ⦋1⦌).app (op k) (oneCoefficient W x y k z)).down := by
      exact congrArg ULift.down hvalue
    _ = JTRealizationGenerators.generator (Input W) (⦋1⦌, k)
          (oneCoefficient W x y k z) ≫
            DaggerSSet.forget.map (chosenG W) := by
      exact congrArg ULift.down hgen

end

end DaggerModels.PartII.JTGtildeGeneratorFiberCalibration
