import DaggerModelsPartII.JTRawFreeInnerOrderedFiber
import DaggerModelsPartII.JTGeneralOrderedFiberWeak
import DaggerModelsPartII.JTProjectiveOrderedFiberComparison

/-!
# The literal raw ordinary JT transpose and its ordered chosen-fiber square

The auxiliary raw transpose uses the original ordinary JT adjunction. Its
comparison with the original chosen transpose is strict. The selected fiber
actions compose only after Kan localization.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRawOrdinaryAdjoint

open JTStrictificationMaps JTStrictificationCoefficients
open JTRawFreeInnerComparison JTGtildeOrderedFiberAction
open JTProjectiveOrderedFiberComparison (row endpoint endpointArrow pRow point)
open JTRightAdjointOrderedFiber
open JTCEOrdinaryFiber OrdinaryJTRealization JTReversalInput
open ChosenHomotopyFiberComparison ChosenHomotopyFiberFunctor

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The literal ordinary JT transpose of the actual raw free-inner unit. -/
def gRawTilde (W : Source) :
    ordinaryInput.obj W ⟶ nerve.obj (rawTarget W).toSSet :=
  realizationNerveAdjunction.homEquiv _ _ (rawG W).hom

/-- The original chosen and raw transposes form the strict adjoint square. -/
theorem transpose_square (W : Source) :
    JTChosenOrdinaryAdjoint.gTilde W ≫ nerve.map (ell W).hom =
      ordinaryInput.map (p.app W) ≫ gRawTilde W := by
  change (realizationNerveAdjunction.homEquiv _ _) (chosenG W).hom ≫
      nerve.map (ell W).hom =
    ordinaryInput.map (p.app W) ≫
      (realizationNerveAdjunction.homEquiv _ _) (rawG W).hom
  symm
  apply realizationNerveAdjunction.homEquiv_naturality_left_square
  change JTProjectiveRealizationMappingWeak.realizedP W ≫ (rawG W).hom =
    (chosenG W).hom ≫ (ell W).hom
  rw [← underlying_projective_map W]
  exact (underlying_square W).symm

/-- The raw transpose restricted to the original raw horizontal row. -/
def gRawRow (W : Source) (m : SimplexCategory) :
    row W m ⟶ ordinaryRow (rawTarget W).toSSet m where
  app k := (gRawTilde W).app (op (m, k.unop))
  naturality {k l} θ := by
    exact (gRawTilde W).naturality
      (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop)))

/-- The strict transpose square on every original horizontal row. -/
theorem row_square (W : Source) (m : SimplexCategory) :
    gRow W m ≫ originalRowMap (ell W).hom m =
      pRow W m ≫ gRawRow W m := by
  apply NatTrans.ext
  funext k z
  exact congrFun (NatTrans.congr_app (transpose_square W) (op (m, k.unop))) z

/-- The raw transpose respects each original ordered outer coface. -/
theorem gRawRow_endpoint (W : Source) (i : Fin 2) :
    endpoint W i ≫ gRawRow W ⦋0⦌ =
      gRawRow W ⦋1⦌ ≫ ordinaryRowEndpoint (rawTarget W).toSSet i := by
  apply NatTrans.ext
  funext k z
  exact congrFun ((gRawTilde W).naturality
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i, 𝟙 k.unop)))) z

/-- The actual product of the two raw-target zero-row maps. -/
def gRawBase (W : Source) :
    row W ⦋0⦌ ⨯ row W ⦋0⦌ ⟶
      ordinaryRow (rawTarget W).toSSet ⦋0⦌ ⨯
        ordinaryRow (rawTarget W).toSSet ⦋0⦌ :=
  prod.map (gRawRow W ⦋0⦌) (gRawRow W ⦋0⦌)

/-- The raw transpose's literal ordered endpoint square. -/
theorem gRawArrow_square (W : Source) :
    endpointArrow W ≫ gRawBase W =
      gRawRow W ⦋1⦌ ≫ ordinaryEndpointArrow (rawTarget W).toSSet := by
  apply prod.hom_ext
  · simpa only [endpointArrow, gRawBase, ordinaryEndpointArrow,
      prod.lift_fst, prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        gRawRow_endpoint W 0
  · simpa only [endpointArrow, gRawBase, ordinaryEndpointArrow,
      prod.lift_snd, prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        gRawRow_endpoint W 1

/-- The strict transpose square on the product of the ordered zero rows. -/
theorem base_square (W : Source) :
    gBase W ≫
        prod.map (originalRowMap (ell W).hom ⦋0⦌)
          (originalRowMap (ell W).hom ⦋0⦌) =
      prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌) ≫ gRawBase W := by
  simp only [gBase, gRawBase, prod.map_map, row_square W ⦋0⦌]

/-- At the two actual `p` images, the raw transpose image point is the
original constant point at the `ell` images of the chosen target vertices. -/
theorem rawPoint_square_at_p (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2 ≫ gRawBase W =
      ordinaryEndpointPoint (rawTarget W)
        ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).1)
        ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).2) := by
  let u := (targetVertices W x y).1
  let v := (targetVertices W x y).2
  calc
    point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2 ≫ gRawBase W =
      (sourcePoint W x y ≫
        prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌)) ≫ gRawBase W := by
        rw [JTProjectiveOrderedFiberComparison.point_square W x y]
    _ = sourcePoint W x y ≫
        (prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌) ≫ gRawBase W) := by
          rw [Category.assoc]
    _ = sourcePoint W x y ≫
        (gBase W ≫ prod.map (originalRowMap (ell W).hom ⦋0⦌)
          (originalRowMap (ell W).hom ⦋0⦌)) := by
            rw [base_square W]
    _ = (sourcePoint W x y ≫ gBase W) ≫
        prod.map (originalRowMap (ell W).hom ⦋0⦌)
          (originalRowMap (ell W).hom ⦋0⦌) := by
            rw [Category.assoc]
    _ = ordinaryEndpointPoint (chosenT W) u v ≫
        prod.map (originalRowMap (ell W).hom ⦋0⦌)
          (originalRowMap (ell W).hom ⦋0⦌) := by
            rw [← imagePoint_eq_ordinaryEndpointPoint W x y]
            rfl
    _ = ordinaryEndpointPoint (rawTarget W)
        ((ell W).hom.app (op ⦋0⦌) u)
        ((ell W).hom.app (op ⦋0⦌) v) :=
          JTGeneralOrderedFiberWeak.endpointPoint_natural (ell W).hom u v

/-- The actual raw transpose's selected chosen-fiber action at the two
literal projective-image vertices, with its target point normalized above. -/
def rawChosenFiberMapAtP (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    chosenFiber (endpointArrow W)
        (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) ⟶
      chosenFiber (ordinaryEndpointArrow (rawTarget W).toSSet)
        (ordinaryEndpointPoint (rawTarget W)
          ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).1)
          ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).2)) :=
  chosenMap (endpointArrow W) (ordinaryEndpointArrow (rawTarget W).toSSet)
    (gRawRow W ⦋1⦌) (gRawBase W) (gRawArrow_square W)
    (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
      (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)
    (ordinaryEndpointPoint (rawTarget W)
      ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).1)
      ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).2))
    (rawPoint_square_at_p W x y)

/-- Both exact selected paths agree after Kan localization. No equality of
the point-set chosen lifts, nor weakness of either unit, is claimed. -/
theorem chosenFiberMap_localized_square (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (weakEquivalences SSet.{0}).Q.map
        (JTGtildeOrderedFiberAction.chosenFiberMap W x y) ≫
      (weakEquivalences SSet.{0}).Q.map
        (JTGeneralOrderedFiberWeak.chosenFiberMap (ell W).hom
          (targetVertices W x y).1 (targetVertices W x y).2) =
    (weakEquivalences SSet.{0}).Q.map
        (JTProjectiveOrderedFiberComparison.chosenFiberMap W x y) ≫
      (weakEquivalences SSet.{0}).Q.map (rawChosenFiberMapAtP W x y) := by
  let u := (targetVertices W x y).1
  let v := (targetVertices W x y).2
  let u' := (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
  let v' := (JTProjectiveOrderedFiberComparison.targetVertices W x y).2
  have hTotal : gRow W ⦋1⦌ ≫ originalRowMap (ell W).hom ⦋1⦌ =
      pRow W ⦋1⦌ ≫ gRawRow W ⦋1⦌ := row_square W ⦋1⦌
  have hBase : gBase W ≫
      prod.map (originalRowMap (ell W).hom ⦋0⦌)
        (originalRowMap (ell W).hom ⦋0⦌) =
      prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌) ≫ gRawBase W := base_square W
  have hLeft := ChosenHomotopyFiberFunctor.chosenMap_comp
    (sourceEndpointArrow W) (ordinaryEndpointArrow (chosenT W).toSSet)
    (ordinaryEndpointArrow (rawTarget W).toSSet)
    (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
    (originalRowMap (ell W).hom ⦋1⦌)
    (prod.map (originalRowMap (ell W).hom ⦋0⦌)
      (originalRowMap (ell W).hom ⦋0⦌))
    (JTGeneralOrderedFiberWeak.rowMap_endpoint (ell W).hom)
    (sourcePoint W x y) (ordinaryEndpointPoint (chosenT W) u v)
    (ordinaryEndpointPoint (rawTarget W)
      ((ell W).hom.app (op ⦋0⦌) u)
      ((ell W).hom.app (op ⦋0⦌) v))
    (imagePoint_eq_ordinaryEndpointPoint W x y)
    (JTGeneralOrderedFiberWeak.endpointPoint_natural (ell W).hom u v)
  have hRight := ChosenHomotopyFiberFunctor.chosenMap_comp
    (sourceEndpointArrow W) (endpointArrow W)
    (ordinaryEndpointArrow (rawTarget W).toSSet)
    (pRow W ⦋1⦌)
    (prod.map (pRow W ⦋0⦌) (pRow W ⦋0⦌))
    (JTProjectiveOrderedFiberComparison.endpoint_square W)
    (gRawRow W ⦋1⦌) (gRawBase W) (gRawArrow_square W)
    (sourcePoint W x y) (point W u' v')
    (ordinaryEndpointPoint (rawTarget W)
      ((ell W).hom.app (op ⦋0⦌) u)
      ((ell W).hom.app (op ⦋0⦌) v))
    (JTProjectiveOrderedFiberComparison.point_square W x y)
    (rawPoint_square_at_p W x y)
  calc
    _ = _ := hLeft
    _ = _ := by simp only [hTotal, hBase]
    _ = _ := hRight.symm

end

end DaggerModels.PartII.JTRawOrdinaryAdjoint
