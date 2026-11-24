import DaggerModelsPartII.NecklaceCylinderJointDiagram
import DaggerModelsPartII.OrderedLabelElements
import DaggerModelsPartII.MovingHomNaturalTransformation
import DaggerModelsPartII.NecklaceCylinderHomSpan

/-!
# The actual decorated original-Hom diagram and its natural span

All native necklace maps and all simplex operators act on the original
rigidified cylinder Homs. The augmentation is a natural map with Kan weak
components. The original descended labels give a full Hom cocone at the
same two raw vertices. No identification with the ordered-label bar or
the original JT flag bar, and no target weakness, is inferred.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedNecklaceHomDiagram

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- The actual ordered-label category, with both operator directions retained. -/
abbrev Index := OrderedLabelElements.Index W (boundaryPoint W x y)

private abbrev p := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev T (i : Index W x y) := OrderedLabelElements.necklace W (boundaryPoint W x y) i
private abbrev k (i : Index W x y) := OrderedLabelElements.degree W (boundaryPoint W x y) i
private abbrev z (i : Index W x y) := OrderedLabelElements.label W (boundaryPoint W x y) i

/-- The SAME cylinders over the actual decorated index. -/
def cylinderDiagram : Index W x y ⥤ SSet.{0} :=
  p W x y ⋙ NecklaceCylinderJointDiagram.cylinderDiagram

/-- The SAME static necklaces over that index. -/
def necklaceDiagram : Index W x y ⥤ SSet.{0} :=
  p W x y ⋙ NecklaceCylinderJointDiagram.necklaceDiagram

private def cylinderFirst (i : Index W x y) :
    (rigidification.obj ((cylinderDiagram W x y).obj i)).Obj :=
  RV ((value (T W x y i)).obj (k W x y i))
    (NecklaceCylinderHomSpan.firstVertex (T W x y i) (k W x y i))

private def cylinderLast (i : Index W x y) :
    (rigidification.obj ((cylinderDiagram W x y).obj i)).Obj :=
  RV ((value (T W x y i)).obj (k W x y i))
    (NecklaceCylinderHomSpan.lastVertex (T W x y i) (k W x y i))

private def necklaceFirst (i : Index W x y) :
    (rigidification.obj ((necklaceDiagram W x y).obj i)).Obj :=
  RV (T W x y i).toSSet (T W x y i).first

private def necklaceLast (i : Index W x y) :
    (rigidification.obj ((necklaceDiagram W x y).obj i)).Obj :=
  RV (T W x y i).toSSet (T W x y i).last

private theorem cylinderFirst_map {i j : Index W x y} (f : i ⟶ j) :
    (rigidification.map ((cylinderDiagram W x y).map f)).obj (cylinderFirst W x y i) =
      cylinderFirst W x y j := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((cylinderDiagram W x y).obj j))
  have h := congrFun (NatTrans.congr_app
    ((Functor.whiskerLeft (p W x y)
      NecklaceCylinderJointDiagram.cylinderBoundary).naturality f) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₀)
  exact h.symm

private theorem cylinderLast_map {i j : Index W x y} (f : i ⟶ j) :
    (rigidification.map ((cylinderDiagram W x y).map f)).obj (cylinderLast W x y i) =
      cylinderLast W x y j := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((cylinderDiagram W x y).obj j))
  have h := congrFun (NatTrans.congr_app
    ((Functor.whiskerLeft (p W x y)
      NecklaceCylinderJointDiagram.cylinderBoundary).naturality f) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₁)
  exact h.symm

private theorem necklaceFirst_map {i j : Index W x y} (f : i ⟶ j) :
    (rigidification.map ((necklaceDiagram W x y).map f)).obj (necklaceFirst W x y i) =
      necklaceFirst W x y j :=
  (vertexEquiv_naturality _ _).trans
    (congrArg (RV (T W x y j).toSSet) (((p W x y).map f).1.first))

private theorem necklaceLast_map {i j : Index W x y} (f : i ⟶ j) :
    (rigidification.map ((necklaceDiagram W x y).map f)).obj (necklaceLast W x y i) =
      necklaceLast W x y j :=
  (vertexEquiv_naturality _ _).trans
    (congrArg (RV (T W x y j).toSSet) (((p W x y).map f).1.last))

/-- The original full rigidified cylinder Hom diagram, with all compositions. -/
def cylinderHomDiagram : Index W x y ⥤ SSet.{0} :=
  homDiagram (cylinderDiagram W x y ⋙ rigidification)
    (cylinderFirst W x y) (cylinderLast W x y)
    (cylinderFirst_map W x y) (cylinderLast_map W x y)

/-- The original full static necklace Hom diagram on the SAME index. -/
def necklaceHomDiagram : Index W x y ⥤ SSet.{0} :=
  homDiagram (necklaceDiagram W x y ⋙ rigidification)
    (necklaceFirst W x y) (necklaceLast W x y)
    (necklaceFirst_map W x y) (necklaceLast_map W x y)

private def rigidifiedAugmentation :
    cylinderDiagram W x y ⋙ rigidification ⟶ necklaceDiagram W x y ⋙ rigidification :=
  Functor.whiskerRight
    (Functor.whiskerLeft (p W x y) NecklaceCylinderJointDiagram.augmentation) rigidification

private theorem augmentation_first (i : Index W x y) :
    ((rigidifiedAugmentation W x y).app i).obj (cylinderFirst W x y i) =
      necklaceFirst W x y i := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV (T W x y i).toSSet)
  have h := congrFun (NatTrans.congr_app
    (NecklaceCylinderAugmentation.augmentation_boundary (T W x y i) (k W x y i))
      (op ⦋0⦌)) (SSet.yonedaEquiv SSet.boundary₁.ι₀)
  change _ = (endpointInclusion (T W x y i)).app (op ⦋0⦌)
    (SSet.yonedaEquiv SSet.boundary₁.ι₀) at h
  exact h.trans (by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₀ ≫
      SSet.boundary₁.desc (T W x y i).first (T W x y i).last) = _
    simp only [SSet.boundary₁.ι₀_desc, Equiv.apply_symm_apply])

private theorem augmentation_last (i : Index W x y) :
    ((rigidifiedAugmentation W x y).app i).obj (cylinderLast W x y i) =
      necklaceLast W x y i := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV (T W x y i).toSSet)
  have h := congrFun (NatTrans.congr_app
    (NecklaceCylinderAugmentation.augmentation_boundary (T W x y i) (k W x y i))
      (op ⦋0⦌)) (SSet.yonedaEquiv SSet.boundary₁.ι₁)
  exact h.trans (by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₁ ≫
      SSet.boundary₁.desc (T W x y i).first (T W x y i).last) = _
    simp only [SSet.boundary₁.ι₁_desc, Equiv.apply_symm_apply])

/-- The actual augmentation is natural on original Homs for the WHOLE index. -/
def leftMap : cylinderHomDiagram W x y ⟶ necklaceHomDiagram W x y :=
  MovingHomNaturalTransformation.homNatTrans
    (F := cylinderDiagram W x y ⋙ rigidification)
    (G := necklaceDiagram W x y ⋙ rigidification)
    (cylinderFirst W x y) (cylinderLast W x y)
    (cylinderFirst_map W x y) (cylinderLast_map W x y)
    (necklaceFirst W x y) (necklaceLast W x y)
    (necklaceFirst_map W x y) (necklaceLast_map W x y)
    (rigidifiedAugmentation W x y) (augmentation_first W x y) (augmentation_last W x y)

/-- Its components are the SAME previously checked actual Hom projections. -/
theorem leftMap_app (i : Index W x y) :
    (leftMap W x y).app i = NecklaceCylinderHomSpan.leftMap (T W x y i) (k W x y i) := rfl

/-- Every component of this full natural map is Kan weak. -/
theorem leftMap_weak (i : Index W x y) : WeakEquivalence ((leftMap W x y).app i) :=
  NecklaceCylinderHomSpan.leftMap_weak (T W x y i) (k W x y i)

/-- Actual descended labels form a cocone, retaining both operator axes. -/
def descendCocone : Cocone (cylinderDiagram W x y) where
  pt := R W
  ι :=
    { app i := descend W x y (T W x y i) (k W x y i) (z W x y i)
      naturality {i j} f := by
        change (nativeMap ((p W x y).map f).1 (k W x y i) ≫
            (value (T W x y j)).map ((p W x y).map f).2) ≫
            descend W x y (T W x y j) (k W x y j) (z W x y j) =
          descend W x y (T W x y i) (k W x y i) (z W x y i) ≫ 𝟙 (R W)
        have h := nativeMap_parameter_natural ((p W x y).map f).1 ((p W x y).map f).2
        change (value (T W x y i)).map ((p W x y).map f).2 ≫
            nativeMap ((p W x y).map f).1 (k W x y j) =
          nativeMap ((p W x y).map f).1 (k W x y i) ≫
            (value (T W x y j)).map ((p W x y).map f).2 at h
        rw [← h, Category.assoc]
        dsimp only [T, k, OrderedLabelElements.necklace, OrderedLabelElements.degree]
        rw [descend_native_natural W x y ((p W x y).map f).1
          (((p W x y).obj j).2) (z W x y j)]
        rw [descend_parameter_natural, Category.comp_id]
        exact congrArg (descend W x y (T W x y i) (k W x y i))
          (OrderedLabelElements.label_map W (boundaryPoint W x y) f) }

private def rigidifiedCocone : Cocone (cylinderDiagram W x y ⋙ rigidification) :=
  rigidification.mapCocone (descendCocone W x y)

private def rawFirst := RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
private def rawLast := RV (R W) (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)

private theorem descend_first (i : Index W x y) :
    ((rigidifiedCocone W x y).ι.app i).obj (cylinderFirst W x y i) = rawFirst W x := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV (R W))
  have h := congrFun (NatTrans.congr_app
    (descend_boundary W x y (T W x y i) (k W x y i) (z W x y i)) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₀)
  exact h.trans (by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)) = _
    simp only [SSet.boundary₁.ι₀_desc, Equiv.apply_symm_apply])

private theorem descend_last (i : Index W x y) :
    ((rigidifiedCocone W x y).ι.app i).obj (cylinderLast W x y i) = rawLast W y := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV (R W))
  have h := congrFun (NatTrans.congr_app
    (descend_boundary W x y (T W x y i) (k W x y i) (z W x y i)) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₁)
  exact h.trans (by
    change SSet.yonedaEquiv (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)) = _
    simp only [SSet.boundary₁.ι₁_desc, Equiv.apply_symm_apply])

/-- The unchanged original raw target Hom at the two specified raw vertices. -/
def rawHom : SSet.{0} := rawFirst W x ⟶[SSet.{0}] rawLast W y

/-- A natural original-Hom cocone to the SAME raw target. -/
def rightMap : cylinderHomDiagram W x y ⟶
    (Functor.const (Index W x y)).obj (rawHom W x y) :=
  (homCocone (cylinderDiagram W x y ⋙ rigidification)
    (cylinderFirst W x y) (cylinderLast W x y)
    (cylinderFirst_map W x y) (cylinderLast_map W x y)
    (rigidifiedCocone W x y) (rawFirst W x) (rawLast W y)
    (descend_first W x y) (descend_last W x y)).ι

/-- The full cocone retains the actual previously checked descended Hom map. -/
theorem rightMap_app (i : Index W x y) :
    (rightMap W x y).app i =
      NecklaceCylinderHomSpan.rightMap W x y (T W x y i) (k W x y i) (z W x y i) := rfl

end

end DaggerModels.PartII.DecoratedNecklaceHomDiagram
