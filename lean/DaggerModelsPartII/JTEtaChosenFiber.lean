import DaggerModelsPartII.JTCEOrdinaryFiber
import DaggerModelsPartII.JTOrdinaryEndpointFibration
import DaggerModelsPartII.ChosenHomotopyFiberFunctor
import DaggerModelsPartII.JTChosenRightMappingUnit

/-!
# The chosen ordinary unit on its original Kan homotopy fiber

The literal original ordinary JT endpoint square of `etaOrdinary` induces a
chosen-fiber map. Both original endpoint arrows are Kan fibrations, and the
already proved strict ordered-fiber map is Kan weak. The actual canonical
strict-to-chosen inclusions identify the two maps and transfer that weakness.
No whole ordinary Joyal weakness of `etaOrdinary` is assumed.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEtaChosenFiber

open JTRightAdjointOrderedFiber JTCEOrdinaryFiber JTChosenOrdinaryAdjoint
open JTChosenCEUnitBoundary JTStrictificationCoefficients
open DaggerModels.PartII.ChosenHomotopyFiberComparison
open DaggerModels.PartII.ChosenHomotopyFiberFunctor
open DaggerModels.PartII.ChosenHomotopyFiberTriangle
open DaggerModels.OrdinaryRigidification.DaggerNerve
open OrdinaryJTRealization

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private abbrev target (W : Source) : DaggerSSet.{0} :=
  daggerCoherentNerve.obj (rigidCoefficient (chosenT W))

private theorem rowEndpoint_naturality {S T : SSet.{0}} (f : S ⟶ T)
    (i : Fin 2) :
    ordinaryRowEndpoint S i ≫ originalRowMap f ⦋0⦌ =
      originalRowMap f ⦋1⦌ ≫ ordinaryRowEndpoint T i := by
  apply NatTrans.ext
  funext k z
  exact congrFun ((nerve.map f).naturality
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i, 𝟙 k.unop)))) z

/-- The source and target are the literal original endpoint arrows, with
the two ordered cofaces preserved by `etaOrdinary`. -/
theorem endpoint_square (W : Source) :
    ordinaryEndpointArrow (chosenT W).toSSet ≫
      prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
        (originalRowMap (etaOrdinary W) ⦋0⦌) =
      originalRowMap (etaOrdinary W) ⦋1⦌ ≫
        ordinaryEndpointArrow (target W).toSSet := by
  change ordinaryEndpointArrow (chosenT W).toSSet ≫
      prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
        (originalRowMap (etaOrdinary W) ⦋0⦌) =
    originalRowMap (etaOrdinary W) ⦋1⦌ ≫
      ordinaryEndpointArrow (chosenNerve W)
  apply prod.hom_ext
  · simpa only [ordinaryEndpointArrow, prod.lift_fst,
      prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        rowEndpoint_naturality (etaOrdinary W) 0
  · simpa only [ordinaryEndpointArrow, prod.lift_snd,
      prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        rowEndpoint_naturality (etaOrdinary W) 1

private theorem vertexPoint_square (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    ordinaryVertexPoint (chosenT W) x y i ≫
        originalRowMap (etaOrdinary W) ⦋0⦌ =
      ordinaryVertexPoint (target W)
        (chosenVertices W x y).1 (chosenVertices W x y).2 i := by
  apply NatTrans.ext
  funext k z
  change ULift.up
      ((CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (GroupoidSimplex.parameter.obj k.unop) ≫
        JTEndpointObjects.boundaryVertexMap i ≫ sourceBoundary W x y) ≫
          etaOrdinary W) =
      ULift.up (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (GroupoidSimplex.parameter.obj k.unop) ≫
        JTEndpointObjects.boundaryVertexMap i ≫ targetBoundary W x y)
  simp only [Category.assoc]
  rw [eta_boundary]

/-- The two original constant vertex points are preserved in order. -/
theorem endpoint_point_square (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    ordinaryEndpointPoint (chosenT W) x y ≫
        prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
          (originalRowMap (etaOrdinary W) ⦋0⦌) =
      ordinaryEndpointPoint (target W)
        (chosenVertices W x y).1 (chosenVertices W x y).2 := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc]
    simp only [ordinaryEndpointPoint, prod.lift_fst]
    exact (vertexPoint_square W x y 0).trans (prod.lift_fst _ _).symm
  · rw [Category.assoc, prod.map_snd, ← Category.assoc]
    simp only [ordinaryEndpointPoint, prod.lift_snd]
    exact (vertexPoint_square W x y 1).trans (prod.lift_snd _ _).symm

private def pointSquare (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    ordinaryEndpointPoint (chosenT W) x y ≫
        prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
          (originalRowMap (etaOrdinary W) ⦋0⦌) =
      ordinaryEndpointPoint (target W)
        (chosenVertices W x y).1 (chosenVertices W x y).2 :=
  endpoint_point_square W x y

/-- The actual selected action on chosen homotopy fibers of the original
ordinary right-adjoint endpoint arrow. -/
def etaChosenFiberMap (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    chosenFiber (ordinaryEndpointArrow (chosenT W).toSSet)
        (ordinaryEndpointPoint (chosenT W) x y) ⟶
      chosenFiber (ordinaryEndpointArrow (target W).toSSet)
        (ordinaryEndpointPoint (target W)
          (chosenVertices W x y).1 (chosenVertices W x y).2) :=
  chosenMap (ordinaryEndpointArrow (chosenT W).toSSet)
    (ordinaryEndpointArrow (target W).toSSet)
    (originalRowMap (etaOrdinary W) ⦋1⦌)
    (prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
      (originalRowMap (etaOrdinary W) ⦋0⦌))
    (endpoint_square W)
    (ordinaryEndpointPoint (chosenT W) x y)
    (ordinaryEndpointPoint (target W)
      (chosenVertices W x y).1 (chosenVertices W x y).2)
    (pointSquare W x y)

private theorem strictFiberMap_eq (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
        (ordinaryEndpointArrow (chosenT W).toSSet)
        (ordinaryEndpointArrow (target W).toSSet)
        (originalRowMap (etaOrdinary W) ⦋1⦌)
        (prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
          (originalRowMap (etaOrdinary W) ⦋0⦌))
        (endpoint_square W)
        (ordinaryEndpointPoint (chosenT W) x y)
        (ordinaryEndpointPoint (target W)
          (chosenVertices W x y).1 (chosenVertices W x y).2)
        (pointSquare W x y) = originalUnitFiberMap W x y := by
  apply pullback.hom_ext
  · simp only [DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
      originalUnitFiberMap_fst]
  · simp only [DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd,
      originalUnitFiberMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The canonical strict-to-chosen inclusions form the exact point-set
triangle with the verified original ordinary unit map. -/
theorem etaChosenFiberMap_inclusion (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    inclusion (ordinaryEndpointArrow (chosenT W).toSSet)
        (ordinaryEndpointPoint (chosenT W) x y) ≫
      etaChosenFiberMap W x y =
    originalUnitFiberMap W x y ≫
      inclusion (ordinaryEndpointArrow (target W).toSSet)
        (ordinaryEndpointPoint (target W)
          (chosenVertices W x y).1 (chosenVertices W x y).2) := by
  rw [← strictFiberMap_eq W x y]
  exact inclusion_chosenMap
    (ordinaryEndpointArrow (chosenT W).toSSet)
    (ordinaryEndpointArrow (target W).toSSet)
    (originalRowMap (etaOrdinary W) ⦋1⦌)
    (prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
      (originalRowMap (etaOrdinary W) ⦋0⦌))
    (endpoint_square W)
    (ordinaryEndpointPoint (chosenT W) x y)
    (ordinaryEndpointPoint (target W)
      (chosenVertices W x y).1 (chosenVertices W x y).2)
    (pointSquare W x y)

/-- The actual chosen unit is Kan weak on its selected original ordinary
homotopy fiber; no whole-map Joyal weakness is used. -/
theorem etaChosenFiberMap_weak (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (etaChosenFiberMap W x y) := by
  letI : (chosenT W).toSSet.Quasicategory := chosenT_quasicategory W
  letI : (target W).toSSet.Quasicategory := by
    change (chosenNerve W).Quasicategory
    exact JTChosenRightMappingUnit.chosenNerve_quasicategory W
  haveI : Fibration (ordinaryEndpointArrow (chosenT W).toSSet) :=
    JTOrdinaryEndpointFibration.ordinaryEndpointArrow_fibration (chosenT W).toSSet
  haveI : Fibration (ordinaryEndpointArrow (target W).toSSet) :=
    JTOrdinaryEndpointFibration.ordinaryEndpointArrow_fibration (target W).toSSet
  haveI : WeakEquivalence (originalUnitFiberMap W x y) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (originalUnitFiberMap_GW W x y)
  rw [← strictFiberMap_eq W x y] at this
  exact chosenMap_weak_of_strict_weak
    (ordinaryEndpointArrow (chosenT W).toSSet)
    (ordinaryEndpointArrow (target W).toSSet)
    (originalRowMap (etaOrdinary W) ⦋1⦌)
    (prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
      (originalRowMap (etaOrdinary W) ⦋0⦌))
    (endpoint_square W)
    (ordinaryEndpointPoint (chosenT W) x y)
    (ordinaryEndpointPoint (target W)
      (chosenVertices W x y).1 (chosenVertices W x y).2)
    (pointSquare W x y)

end

end DaggerModels.PartII.JTEtaChosenFiber
