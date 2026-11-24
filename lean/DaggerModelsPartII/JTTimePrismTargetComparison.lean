import DaggerModelsPartII.JTCompatibleTimePrisms
import DaggerModelsPartII.JTCylinderOverTargetBaseChange
import DaggerModelsPartII.JTCylinderOverTargetReindex
import DaggerModelsPartII.JTInterpolatedCylinderOutput
import DaggerModelsPartII.JTInterpolatedCylinderReindex
import DaggerModelsPartII.JTGraphInterpolatedOverTime

/-! A compatible time-prism family maps into the actual fixed-target comma. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTimePrismTargetComparison

open JTCompatibleTimePrisms (Family)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTRealizedLabelEndpoints
open JTNecklaceEndpointCylinder
open JTInterpolatedReducedCylinder (cylinderMap cylinderMap_cylinder cylinderMap_boundary)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_boundary)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphInterpolatedCollapseOriginal (timeCollapse)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {time : A ⥤ SimplexCategory}
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {T : NecklaceCode} {c : T ⟶ Q.code}
variable (F : Family time Q T c)

private abbrev k (a : A) := F.coefficient.obj a
private abbrev b := boundaryPoint W x y
private abbrev P := OrderedLabelElements.labelPresheaf W (b (x := x) (y := y))
private abbrev I := DecoratedNecklaceHomDiagram.Index W x y
private abbrev lbl (a : A) : I (x := x) (y := y) :=
  OrderedLabelElements.mk W (b (x := x) (y := y)) T (k F a) (F.label a)

private def labelMap {a a' : A} (f : a ⟶ a') : lbl F a ⟶ lbl F a' := by
  let h : (T, k F a) ⟶ (T, k F a') := (𝟙 T, F.coefficient.map f)
  refine (CategoryOfElements.homMk
    ((P (x := x) (y := y)).elementsMk (op (T, k F a')) (F.label a'))
    ((P (x := x) (y := y)).elementsMk (op (T, k F a)) (F.label a))
    h.op ?_).op
  let G := orderedNecklaceLabels W (b (x := x) (y := y))
  change (G.obj (op T)).map (F.coefficient.map f).op
    ((G.map (𝟙 (op T))).app (op (k F a')) (F.label a')) = F.label a
  rw [G.map_id]
  exact F.label_map f

private abbrev projection := OrderedLabelElements.projection W (b (x := x) (y := y))

private instance : (projection (W := W) (x := x) (y := y)).Faithful := by
  change ((CategoryOfElements.π (P (W := W) (x := x) (y := y))).leftOp).Faithful
  infer_instance

/-- The family retains the literal decorated operators. -/
def toLabels : A ⥤ I (x := x) (y := y) where
  obj := lbl F
  map := labelMap F
  map_id a := by
    apply (projection (W := W) (x := x) (y := y)).map_injective
    change (𝟙 T, F.coefficient.map (𝟙 a)) = (𝟙 T, 𝟙 (k F a))
    rw [F.coefficient.map_id]
  map_comp f g := by
    apply (projection (W := W) (x := x) (y := y)).map_injective
    rw [Functor.map_comp]
    change (𝟙 T, F.coefficient.map (f ≫ g)) =
      (𝟙 T ≫ 𝟙 T, F.coefficient.map f ≫ F.coefficient.map g)
    rw [F.coefficient.map_comp, Category.id_comp]

private theorem under_map {a a' : A} (f : a ⟶ a') :
    (underDiagram W x y).map ((toLabels F).map f) = (under T).map (F.coefficient.map f) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 T) (k F a) ≫ (value T).map (F.coefficient.map f) = _
  rw [nativeMap_id, Category.id_comp]
  rfl

/-- The complete map from the native time cylinder into its decorated cylinder. -/
def cylinderAt (a : A) :
    (under T).obj (time.obj a) ⟶ (underDiagram W x y).obj (lbl F a) :=
  Under.homMk (cylinderMap T (F.parameter a)) (cylinderMap_boundary T (F.parameter a))

private theorem rawEquation (a : A) :
    (cylinderAt F a).right ≫ ((underCocone W x y).app (lbl F a)).right =
      augmentation T (time.obj a) ≫ c.map ≫ Q.map := by
  let n := time.obj a
  let z := F.label a
  change cylinderMap T (F.parameter a) ≫ descend W x y T (k F a) z = _
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, descend_cylinder,
      ← Category.assoc ((cylinder T).app n), augmentation_cylinder]
    exact F.raw a
  · rw [← Category.assoc, cylinderMap_boundary, descend_boundary,
      ← Category.assoc ((boundary T).app n), augmentation_boundary,
      ← Category.assoc (endpointInclusion T), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, Q.first, Q.last]

private theorem cylinder_natural {a a' : A} (f : a ⟶ a') :
    cylinderAt F a ≫ (underDiagram W x y).map ((toLabels F).map f) =
      (under T).map (time.map f) ≫ cylinderAt F a' := by
  rw [under_map F f]
  apply Under.UnderMorphism.ext
  change cylinderMap T (F.parameter a) ≫ (value T).map (F.coefficient.map f) =
    (value T).map (time.map f) ≫ cylinderMap T (F.parameter a')
  rw [JTInterpolatedCylinderOutput.cylinderMap_output,
    JTInterpolatedCylinderReindex.cylinderMap_reindex, F.parameter_map f]

private abbrev D := JTTargetCommaPullback.diagram W x y Q

/-- The whole native and decorated pullback legs agree along each time operator. -/
def liftNatural : time ⋙ under T ⟶ toLabels F ⋙ D (Q := Q) where
  app a := JTCylinderOverTarget.lift W x y Q (lbl F a) T (time.obj a)
    (cylinderAt F a) c (rawEquation F a)
  naturality {a a'} f :=
    (JTCylinderOverTargetBaseChange.lift_compare W x y Q (lbl F a) (lbl F a') T T _ _
      (cylinderAt F a) (cylinderAt F a') c c (rawEquation F a) (rawEquation F a')
      ((under T).map (time.map f)) ((toLabels F).map f) (cylinder_natural F f)
      (JTCylinderOverTargetReindex.native_reindex W x y Q T _ _ (time.map f) c).symm).symm

/-- Every actual internal necklace at every time maps to the same original
fixed-target comma, keeping its whole map over both endpoints. -/
def toComma : BoundaryNecklaceComma.Presentation (time ⋙ under T) ⥤
    CostructuredArrow (toTarget W x y) Q :=
  JTBoundaryNecklacePresentationCone.mapPresentation (D (Q := Q))
    (time ⋙ under T) (toLabels F) (liftNatural F) ⋙
    (JTTargetCommaPullback.equivalence W x y Q).inverse

variable (U : TargetComma Q) (g : T ⟶ U.left.fiber.left)

/-- An arrow out of a fixed family requires every decorated target joint to
be hit by a joint of the family's fixed decorated code. -/
theorem target_joints_card_le
    (P : BoundaryNecklaceComma.Presentation (time ⋙ under T))
    (f : (toComma F).obj P ⟶ U) :
    (JTGraphLiftTransport.code U.left).joints.card ≤ T.joints.card := by
  let e := JTTargetCommaPullback.equivalence W x y Q
  let K := JTBoundaryNecklacePresentationCone.mapPresentation (D (Q := Q))
    (time ⋙ under T) (toLabels F) (liftNatural F)
  let a := (e.counitIso.app (K.obj P)).inv ≫ e.functor.map f
  let j : T ⟶ JTGraphLiftTransport.code U.left :=
    ((OrderedLabelElements.projection W (b (x := x) (y := y))).map a.base).1
  exact (Finset.card_le_card (NecklaceCode.joints_subset_image j)).trans Finset.card_image_le

private def nativeCocone : time ⋙ under T ⟶ (Functor.const A).obj
    (BoundaryNecklaceComma.necklaceUnder.obj U.left.fiber.left) where
  app a := timeCollapse (n := time.obj a) g
  naturality {a a'} f := by
    change (under T).map (time.map f) ≫ timeCollapse (n := time.obj a') g =
      timeCollapse (n := time.obj a) g ≫ 𝟙 _
    rw [Category.comp_id]
    exact JTGraphInterpolatedOverTime.timeCollapse_reindex g (time.map f)

private theorem lift_app (a : A) : (liftNatural F).app a =
    JTCylinderOverTarget.lift W x y Q (lbl F a) T (time.obj a)
      (cylinderAt F a) c (rawEquation F a) := rfl

private theorem native_app (a : A) : (nativeCocone U g).app a =
    timeCollapse (n := time.obj a) g := rfl

private theorem target_app :
    ((JTTargetCommaPullback.toPullback W x y Q).obj U).fiber.hom =
      JTTargetCommaPullback.lift W x y Q U := rfl

private theorem comparison_square
    (α : toLabels F ⟶ (Functor.const A).obj U.left.base)
    (hα : ∀ a, cylinderAt F a ≫ (underDiagram W x y).map (α.app a) =
      timeCollapse (n := time.obj a) g ≫ U.left.fiber.hom)
    (hg : g ≫ U.hom.hom = c) (a : A) :
    (liftNatural F).app a ≫ (D (Q := Q)).map (α.app a) =
      (nativeCocone U g).app a ≫ ((JTTargetCommaPullback.toPullback W x y Q).obj U).fiber.hom := by
  rw [lift_app, native_app, target_app]
  apply pullback.hom_ext (f := (underCocone W x y).app U.left.base)
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q U.left.base =
      (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q U.left.base
    have hf := JTTargetCommaPullback.map_fst W x y Q
      (i := lbl F a) (j := U.left.base) (α.app a)
    rw [Category.assoc, hf, ← Category.assoc,
      JTCylinderOverTarget.lift_decorated, Category.assoc, JTTargetCommaPullback.lift_fst]
    exact hα a
  · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q U.left.base =
      (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q U.left.base
    have hs := JTTargetCommaPullback.map_snd W x y Q
      (i := lbl F a) (j := U.left.base) (α.app a)
    rw [Category.assoc, hs, JTCylinderOverTarget.lift_native,
      Category.assoc, JTTargetCommaPullback.lift_snd]
    apply Under.UnderMorphism.ext
    change augmentation T (time.obj a) ≫ c.map =
      (augmentation T (time.obj a) ≫ g.map) ≫ U.hom.hom.map
    rw [Category.assoc]
    exact congrArg (fun v : T ⟶ Q.code ↦ augmentation T (time.obj a) ≫ v.map) hg.symm

/-- Compatible decorated operators and a factorization of the original native
collapse give a cone to the specified original comma object. -/
def comparisonToOriginal
    (α : toLabels F ⟶ (Functor.const A).obj U.left.base)
    (hα : ∀ a, cylinderAt F a ≫ (underDiagram W x y).map (α.app a) =
      timeCollapse (n := time.obj a) g ≫ U.left.fiber.hom)
    (hg : g ≫ U.hom.hom = c) :
    toComma F ⟶ (Functor.const (BoundaryNecklaceComma.Presentation (time ⋙ under T))).obj U :=
  JTBoundaryNecklaceConeReindex.mapCone
    (JTBoundaryNecklacePresentationCone.coneFromVariableDiagram (D (Q := Q))
      ((JTTargetCommaPullback.toPullback W x y Q).obj U) (time ⋙ under T)
      (toLabels F) (liftNatural F) α (nativeCocone U g) (comparison_square F U g α hα hg))
    (JTTargetCommaPullback.equivalence W x y Q).inverse
    ((JTTargetCommaPullback.equivalence W x y Q).unitIso.app U).inv

end

end DaggerModels.PartII.JTTimePrismTargetComparison
