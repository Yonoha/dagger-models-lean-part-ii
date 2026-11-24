import DaggerModelsPartII.DecoratedNecklaceHomDiagram
import DaggerModelsPartII.DecoratedNecklaceHomBar
import DaggerModelsPartII.JTRawSingleOrderedLabelIso
import DaggerModelsPartII.JTRawFreeInnerComparison
import DaggerModelsPartII.ReplacementConstantSections

/-!
# Postcompose the actual decorated Hom cocone by the original raw unit

The component equality uses the same descended label, cylinder, and endpoint
transports. At the projective-image pair the existing one-edge pushout equality
identifies the complete casted Hom map. The raw unit's rigidification Hom map
is weak by Part I; evaluator and raw JT chosen-fiber weakness remain open.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerChosenRigidificationNecklace
open DaggerNativeSimplicialReplacement
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedRawUnitHomCalibration

open JTProjectiveOrderedFiberComparison (row pRow targetVertices)
open JTGtildeOrderedFiberAction (sourceRow)
open JTRawFreeInnerComparison (rawG rawTarget ell)
open JTRawSingleOrderedLabelIso (nativeLabelOfRawFiber same_simplex_descended_map
  rawG_zeroGenerator_at_p)
open JTNecklaceEndpointCylinder (value descend descend_boundary)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private def rawVertex (W : Source) (a : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (rigidification.obj (R W)).Obj :=
  RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W a)

private def targetVertex (W : Source)
    (x : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (rigidification.obj (rawTarget W).toSSet).Obj :=
  RV (rawTarget W).toSSet
    ((ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertex W
        ((JTGtildeOrderedFiberAction.gRow W ⦋0⦌).app (op ⦋0⦌) x)))

private theorem rawG_vertex (W : Source)
    (x : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (rigidification.map (rawG W).hom).obj
      (rawVertex W ((pRow W ⦋0⦌).app (op ⦋0⦌) x)) = targetVertex W x := by
  exact (vertexEquiv_naturality (rawG W).hom _).trans
    (congrArg (RV (rawTarget W).toSSet) (rawG_zeroGenerator_at_p W x))

/-- The actual raw-unit Hom map at the two original projective-image vertices. -/
def rawGHomAtP (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    DecoratedNecklaceHomDiagram.rawHom W (targetVertices W x y).1
        (targetVertices W x y).2 ⟶
      (targetVertex W x ⟶[SSet.{0}] targetVertex W y) :=
  castMap (rigidification.map (rawG W).hom)
    (rawVertex W (targetVertices W x y).1)
    (rawVertex W (targetVertices W x y).2)
    (targetVertex W x) (targetVertex W y)
    (rawG_vertex W x) (rawG_vertex W y)

/-- Part I already proves weakness of this rigidification Hom map of the raw
free-inner unit. This is not the raw JT chosen-fiber action. -/
theorem rawGHomAtP_weak (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (rawGHomAtP W x y) := by
  apply (DaggerActualRigHomWeakCoreRigidification.castMap_weak_iff _ _ _ _ _ _ _).mpr
  exact DaggerActualInnerAnodyneRigidification.hom_weak (rawG W).hom
    (JTFreeInnerUnderlying.unit_underlying_innerAnodyne
      (DaggerJTRealization.daggerRealization.obj W)) _ _

/-- Postcomposition of the entire decorated original-Hom natural cocone. -/
def postRawRightMapAtP (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    DecoratedNecklaceHomDiagram.cylinderHomDiagram W
        (targetVertices W x y).1 (targetVertices W x y).2 ⟶
      (Functor.const (DecoratedNecklaceHomDiagram.Index W
        (targetVertices W x y).1 (targetVertices W x y).2)).obj
          (targetVertex W x ⟶[SSet.{0}] targetVertex W y) :=
  DecoratedNecklaceHomDiagram.rightMap W
      (targetVertices W x y).1 (targetVertices W x y).2 ≫
    (Functor.const (DecoratedNecklaceHomDiagram.Index W
      (targetVertices W x y).1 (targetVertices W x y).2)).map (rawGHomAtP W x y)

/-- Postcompose the ACTUAL whole decorated evaluator at the same raw pair. -/
def wholeBarPostRawAtP (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    DecoratedNecklaceHomBar.cylinderBar W
        (targetVertices W x y).1 (targetVertices W x y).2 ⟶
      (targetVertex W x ⟶[SSet.{0}] targetVertex W y) :=
  DecoratedNecklaceHomBar.evaluator W
      (targetVertices W x y).1 (targetVertices W x y).2 ≫ rawGHomAtP W x y

/-- The whole actual postcomposed bar map is weak exactly when its original
evaluator is weak. Neither of these remaining weaknesses is proved here. -/
theorem wholeBarPostRaw_weak_iff (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (wholeBarPostRawAtP W x y) ↔
      WeakEquivalence (DecoratedNecklaceHomBar.evaluator W
        (targetVertices W x y).1 (targetVertices W x y).2) := by
  have : WeakEquivalence (rawGHomAtP W x y) := rawGHomAtP_weak W x y
  exact weakEquivalence_postcomp_iff _ _

/-- The whole-bar postcomposition is the augmentation of the same
postcomposed natural Hom cocone, on every decorated chain and coefficient. -/
theorem wholeBarPostRaw_augmentation (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    wholeBarPostRawAtP W x y =
      diagonalAugmentation
        (DecoratedNecklaceHomDiagram.cylinderHomDiagram W
          (targetVertices W x y).1 (targetVertices W x y).2)
        (postRawRightMapAtP W x y) := by
  exact ReplacementConstantSections.augmentation_postcompose
    (DecoratedNecklaceHomDiagram.cylinderHomDiagram W
      (targetVertices W x y).1 (targetVertices W x y).2)
    (DecoratedNecklaceHomDiagram.rightMap W
      (targetVertices W x y).1 (targetVertices W x y).2)
    (rawGHomAtP W x y)

/-- On a constant decorated chain, the whole-bar map is exactly its
original component map, retaining its entire Hom simplex. -/
theorem wholeBarPostRaw_section (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (i : DecoratedNecklaceHomDiagram.Index W
      (targetVertices W x y).1 (targetVertices W x y).2) :
    ReplacementConstantSections.sectionMap
        (DecoratedNecklaceHomDiagram.cylinderHomDiagram W
          (targetVertices W x y).1 (targetVertices W x y).2) i ≫
      wholeBarPostRawAtP W x y = (postRawRightMapAtP W x y).app i := by
  rw [wholeBarPostRaw_augmentation]
  exact ReplacementConstantSections.section_augmentation _ _ i

private theorem descend_first (W : Source)
    (a d : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode)
    (k : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (boundaryPoint W a d)).obj (op T)).obj (op k)) :
    (rigidification.map (descend W a d T k z)).obj
      (RV ((value T).obj k) (NecklaceCylinderHomSpan.firstVertex T k)) =
        rawVertex W a := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV (R W))
  have h := congrFun (NatTrans.congr_app
    (descend_boundary W a d T k z) (op ⦋0⦌))
      (SSet.yonedaEquiv SSet.boundary₁.ι₀)
  exact h.trans (by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W a)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W d)) = _
    simp only [SSet.boundary₁.ι₀_desc, Equiv.apply_symm_apply])

private theorem descend_last (W : Source)
    (a d : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode)
    (k : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (boundaryPoint W a d)).obj (op T)).obj (op k)) :
    (rigidification.map (descend W a d T k z)).obj
      (RV ((value T).obj k) (NecklaceCylinderHomSpan.lastVertex T k)) =
        rawVertex W d := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV (R W))
  have h := congrFun (NatTrans.congr_app
    (descend_boundary W a d T k z) (op ⦋0⦌))
      (SSet.yonedaEquiv SSet.boundary₁.ι₁)
  exact h.trans (by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W a)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W d)) = _
    simp only [SSet.boundary₁.ι₁_desc, Equiv.apply_symm_apply])

private theorem composite_first (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode)
    (k : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (boundaryPoint W (targetVertices W x y).1 (targetVertices W x y).2)).obj
        (op T)).obj (op k)) :
    (rigidification.map (descend W (targetVertices W x y).1
      (targetVertices W x y).2 T k z ≫ (rawG W).hom)).obj
        (RV ((value T).obj k) (NecklaceCylinderHomSpan.firstVertex T k)) =
      targetVertex W x := by
  rw [rigidification.map_comp]
  exact (congrArg (rigidification.map (rawG W).hom).obj
    (descend_first W _ _ T k z)).trans (rawG_vertex W x)

private theorem composite_last (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode)
    (k : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (boundaryPoint W (targetVertices W x y).1 (targetVertices W x y).2)).obj
        (op T)).obj (op k)) :
    (rigidification.map (descend W (targetVertices W x y).1
      (targetVertices W x y).2 T k z ≫ (rawG W).hom)).obj
        (RV ((value T).obj k) (NecklaceCylinderHomSpan.lastVertex T k)) =
      targetVertex W y := by
  rw [rigidification.map_comp]
  exact (congrArg (rigidification.map (rawG W).hom).obj
    (descend_last W _ _ T k z)).trans (rawG_vertex W y)

/-- One complete casted Hom map for the SAME descended cylinder and raw unit. -/
def compositeHomAtP (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode)
    (k : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (boundaryPoint W (targetVertices W x y).1 (targetVertices W x y).2)).obj
        (op T)).obj (op k)) :
    NecklaceCylinderHomSpan.cylinderHom T k ⟶
      (targetVertex W x ⟶[SSet.{0}] targetVertex W y) :=
  castMap (rigidification.map (descend W (targetVertices W x y).1
      (targetVertices W x y).2 T k z ≫ (rawG W).hom))
    (RV ((value T).obj k) (NecklaceCylinderHomSpan.firstVertex T k))
    (RV ((value T).obj k) (NecklaceCylinderHomSpan.lastVertex T k))
    (targetVertex W x) (targetVertex W y)
    (composite_first W x y T k z) (composite_last W x y T k z)

/-- The actual component of the full cocone is exactly this composite Hom map. -/
theorem postRawRightMapAtP_app (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (i : DecoratedNecklaceHomDiagram.Index W
      (targetVertices W x y).1 (targetVertices W x y).2) :
    (postRawRightMapAtP W x y).app i =
      compositeHomAtP W x y
        (OrderedLabelElements.necklace W
          (boundaryPoint W (targetVertices W x y).1 (targetVertices W x y).2) i)
        (OrderedLabelElements.degree W
          (boundaryPoint W (targetVertices W x y).1 (targetVertices W x y).2) i)
        (OrderedLabelElements.label W
          (boundaryPoint W (targetVertices W x y).1 (targetVertices W x y).2) i) := by
  let a := (targetVertices W x y).1
  let d := (targetVertices W x y).2
  let T := OrderedLabelElements.necklace W (boundaryPoint W a d) i
  let k := OrderedLabelElements.degree W (boundaryPoint W a d) i
  let z := OrderedLabelElements.label W (boundaryPoint W a d) i
  rw [show (postRawRightMapAtP W x y).app i =
      (DecoratedNecklaceHomDiagram.rightMap W a d).app i ≫ rawGHomAtP W x y from rfl]
  rw [DecoratedNecklaceHomDiagram.rightMap_app]
  have hc := castMap_comp
    (rigidification.map (descend W a d T k z))
    (rigidification.map (rawG W).hom)
    (RV ((value T).obj k) (NecklaceCylinderHomSpan.firstVertex T k))
    (RV ((value T).obj k) (NecklaceCylinderHomSpan.lastVertex T k))
    (rawVertex W a) (rawVertex W d)
    (targetVertex W x) (targetVertex W y)
    (descend_first W a d T k z) (descend_last W a d T k z)
    (rawG_vertex W x) (rawG_vertex W y)
  change castMap
      (rigidification.map (descend W a d T k z) ≫
        rigidification.map (rawG W).hom) _ _ _ _ _ _ =
    NecklaceCylinderHomSpan.rightMap W a d T k z ≫ rawGHomAtP W x y at hc
  apply Eq.trans hc.symm
  exact castMap_congr
    (rigidification.map_comp (descend W a d T k z) (rawG W).hom).symm
    _ _ _ _ _ _ _ _

/-- At the same original one-edge coefficient, the complete postcomposed
rigidification Hom map is cast from the checked complete CE comparison. -/
theorem single_postRaw_eq_CE (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (JTProjectiveOrderedFiberComparison.endpointArrow W)
      (JTProjectiveOrderedFiberComparison.point W
        (targetVertices W x y).1 (targetVertices W x y).2)).obj (op k)) :
    let a := targetVertices W x y
    let u := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).1
    let v := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).2
    let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
      (op k)) ((JTRawUnitCylinderCalibration.rawStrictFiberMapAtP W x y).app
        (op k) z)
    compositeHomAtP W x y (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
      (nativeLabelOfRawFiber W a.1 a.2 k z) =
      castMap (rigidification.map
        (JTRawUnitCylinderCalibration.singleCylinderToCE k ≫ f.right))
        (RV ((value (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)).obj k)
          (NecklaceCylinderHomSpan.firstVertex
            (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k))
        (RV ((value (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)).obj k)
          (NecklaceCylinderHomSpan.lastVertex
            (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k))
        (targetVertex W x) (targetVertex W y)
        (by
          rw [← same_simplex_descended_map W x y k z]
          exact composite_first W x y
            (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
            (nativeLabelOfRawFiber W a.1 a.2 k z))
        (by
          rw [← same_simplex_descended_map W x y k z]
          exact composite_last W x y
            (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
            (nativeLabelOfRawFiber W a.1 a.2 k z)) := by
  dsimp only
  apply castMap_congr
    (congrArg rigidification.map (same_simplex_descended_map W x y k z))
    _ _ _ _ _ _ _ _

end

end DaggerModels.PartII.DecoratedRawUnitHomCalibration
