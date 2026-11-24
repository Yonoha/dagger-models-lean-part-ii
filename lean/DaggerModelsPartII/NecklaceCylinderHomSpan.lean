import DaggerModelsPartII.NecklaceCylinderAugmentation
import DaggerModelsPartII.ReducedCylinderEndpointHomWeak
import ActualRigHomWeakCoreRigidification

/-!
# An actual original-Hom span for every ordered necklace label

The left leg is the original rigidified augmentation at the two actual
boundary vertices and is Kan weak. The right leg is the original rigidified
descended label at the SAME raw vertices. This gives a localized component
map, not yet a higher coherent comparison of decorated bar constructions.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerChosenRigidificationNecklace
open DaggerModels.OriginalOrdinaryMovingHomColimits
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.NecklaceCylinderHomSpan

open JTNecklaceEndpointCylinder
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := NecklaceCode
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private def firstBoundary : B.obj (op ⦋0⦌) := SSet.yonedaEquiv SSet.boundary₁.ι₀
private def lastBoundary : B.obj (op ⦋0⦌) := SSet.yonedaEquiv SSet.boundary₁.ι₁

/-- The original cylinder's first ordered boundary vertex. -/
def firstVertex (T : NCode) (k : SimplexCategory) :
    ((value T).obj k).obj (op ⦋0⦌) :=
  ((boundary T).app k).app (op ⦋0⦌) firstBoundary

/-- The original cylinder's last ordered boundary vertex. -/
def lastVertex (T : NCode) (k : SimplexCategory) :
    ((value T).obj k).obj (op ⦋0⦌) :=
  ((boundary T).app k).app (op ⦋0⦌) lastBoundary

/-- The SAME original rigidification Hom at those two vertices. -/
def cylinderHom (T : NCode) (k : SimplexCategory) : SSet.{0} :=
  RV ((value T).obj k) (firstVertex T k) ⟶[SSet.{0}]
    RV ((value T).obj k) (lastVertex T k)

/-- The original static outer Hom of the SAME native necklace. -/
def necklaceHom (T : NCode) : SSet.{0} :=
  RV T.toSSet T.first ⟶[SSet.{0}] RV T.toSSet T.last

private theorem augmentation_first (T : NCode) (k : SimplexCategory) :
    (NecklaceCylinderAugmentation.augmentation T k).app (op ⦋0⦌)
      (firstVertex T k) = T.first := by
  have h := congrFun (NatTrans.congr_app
    (NecklaceCylinderAugmentation.augmentation_boundary T k) (op ⦋0⦌)) firstBoundary
  change (NecklaceCylinderAugmentation.augmentation T k).app (op ⦋0⦌)
      (firstVertex T k) = (endpointInclusion T).app (op ⦋0⦌) firstBoundary at h
  rw [h]
  change SSet.yonedaEquiv (SSet.boundary₁.ι₀ ≫ endpointInclusion T) = T.first
  change SSet.yonedaEquiv
      (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last) = T.first
  simp only [SSet.boundary₁.ι₀_desc, Equiv.apply_symm_apply]

private theorem augmentation_last (T : NCode) (k : SimplexCategory) :
    (NecklaceCylinderAugmentation.augmentation T k).app (op ⦋0⦌)
      (lastVertex T k) = T.last := by
  have h := congrFun (NatTrans.congr_app
    (NecklaceCylinderAugmentation.augmentation_boundary T k) (op ⦋0⦌)) lastBoundary
  change (NecklaceCylinderAugmentation.augmentation T k).app (op ⦋0⦌)
      (lastVertex T k) = (endpointInclusion T).app (op ⦋0⦌) lastBoundary at h
  rw [h]
  change SSet.yonedaEquiv
      (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last) = T.last
  simp only [SSet.boundary₁.ι₁_desc, Equiv.apply_symm_apply]

private def leftFirst (T : NCode) (k : SimplexCategory) :
    (rigidification.map (NecklaceCylinderAugmentation.augmentation T k)).obj
        (RV ((value T).obj k) (firstVertex T k)) = RV T.toSSet T.first :=
  (vertexEquiv_naturality _ _).trans
    (congrArg (RV T.toSSet) (augmentation_first T k))

private def leftLast (T : NCode) (k : SimplexCategory) :
    (rigidification.map (NecklaceCylinderAugmentation.augmentation T k)).obj
        (RV ((value T).obj k) (lastVertex T k)) = RV T.toSSet T.last :=
  (vertexEquiv_naturality _ _).trans
    (congrArg (RV T.toSSet) (augmentation_last T k))

/-- The actual original augmentation Hom map, with BOTH endpoint transports. -/
def leftMap (T : NCode) (k : SimplexCategory) : cylinderHom T k ⟶ necklaceHom T :=
  castMap (rigidification.map (NecklaceCylinderAugmentation.augmentation T k))
    (RV ((value T).obj k) (firstVertex T k)) (RV ((value T).obj k) (lastVertex T k))
    (RV T.toSSet T.first) (RV T.toSSet T.last) (leftFirst T k) (leftLast T k)

/-- The SAME boundary-pair Hom projection is Kan weak, without a Mono premise. -/
theorem leftMap_weak (T : NCode) (k : SimplexCategory) : WeakEquivalence (leftMap T k) := by
  apply (DaggerActualRigHomWeakCoreRigidification.castMap_weak_iff _ _ _ _ _ _ _).2
  exact ReducedCylinderEndpointHomWeak.augmentation_endpointHom_weak
    (endpointInclusion T) k firstBoundary lastBoundary

private theorem descend_first (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (descend W x y T k z).app (op ⦋0⦌) (firstVertex T k) =
      JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x := by
  have h := congrFun (NatTrans.congr_app
    (descend_boundary W x y T k z) (op ⦋0⦌)) firstBoundary
  change (descend W x y T k z).app (op ⦋0⦌) (firstVertex T k) =
      (rawBoundary W x y).app (op ⦋0⦌) firstBoundary at h
  rw [h]
  change SSet.yonedaEquiv (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc
    (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
    (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)) = _
  simp only [SSet.boundary₁.ι₀_desc, Equiv.apply_symm_apply]

private theorem descend_last (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (descend W x y T k z).app (op ⦋0⦌) (lastVertex T k) =
      JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y := by
  have h := congrFun (NatTrans.congr_app
    (descend_boundary W x y T k z) (op ⦋0⦌)) lastBoundary
  change (descend W x y T k z).app (op ⦋0⦌) (lastVertex T k) =
      (rawBoundary W x y).app (op ⦋0⦌) lastBoundary at h
  rw [h]
  change SSet.yonedaEquiv (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc
    (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
    (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)) = _
  simp only [SSet.boundary₁.ι₁_desc, Equiv.apply_symm_apply]

/-- The actual descended-label Hom map at the SAME two raw target vertices. -/
def rightMap (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    cylinderHom T k ⟶
      (RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) ⟶[SSet.{0}]
        RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)) :=
  castMap (rigidification.map (descend W x y T k z))
    (RV ((value T).obj k) (firstVertex T k)) (RV ((value T).obj k) (lastVertex T k))
    (RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x))
    (RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y))
    ((vertexEquiv_naturality _ _).trans (congrArg (RV (R W)) (descend_first W x y T k z)))
    ((vertexEquiv_naturality _ _).trans (congrArg (RV (R W)) (descend_last W x y T k z)))

/-- The actual left leg is invertible AFTER Kan localization. -/
def leftIso (T : NCode) (k : SimplexCategory) :
    (weakEquivalences SSet.{0}).Q.obj (cylinderHom T k) ≅
      (weakEquivalences SSet.{0}).Q.obj (necklaceHom T) := by
  have : WeakEquivalence (leftMap T k) := leftMap_weak T k
  have : IsIso ((weakEquivalences SSet.{0}).Q.map (leftMap T k)) :=
    Localization.inverts _ _ _ (mem_weakEquivalences (leftMap T k))
  exact asIso ((weakEquivalences SSet.{0}).Q.map (leftMap T k))

/-- A localized COMPONENT map of the original-Hom span; no bar coherence
or target weakness is inferred from this pointwise inversion. -/
def localizedComponent (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (weakEquivalences SSet.{0}).Q.obj (necklaceHom T) ⟶
      (weakEquivalences SSet.{0}).Q.obj
        (RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) ⟶[SSet.{0}]
          RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)) :=
  (leftIso T k).inv ≫ (weakEquivalences SSet.{0}).Q.map (rightMap W x y T k z)

end

end DaggerModels.PartII.NecklaceCylinderHomSpan
