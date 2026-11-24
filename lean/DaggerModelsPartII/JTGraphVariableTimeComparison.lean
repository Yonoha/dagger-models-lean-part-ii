import DaggerModelsPartII.JTGraphVariableTimeTraversal
import DaggerModelsPartII.JTPointwisePullbackLift

/-! The full variable-source graph resolution compares inside the original slice. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphVariableTimeComparison

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex
open JTGraphVariableTimeTraversal (labels cylinders)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open BoundaryNecklaceComma (necklaceUnder)
open JTGraphInterpolatedRaw (toDecorated)
open JTGraphInterpolatedCollapseOriginal (timeCollapse)
open NecklaceCylinderAugmentation (augmentation)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q)

private abbrev E := JTTargetCommaPullback.diagram W x y Q

private abbrev A := Index U

private def fst : labels U ⋙ E (Q := Q) ⟶ labels U ⋙ underDiagram W x y where
  app P := JTTargetCommaPullback.fst W x y Q ((labels U).obj P)
  naturality {_ _} f := JTTargetCommaPullback.map_fst W x y Q ((labels U).map f)

private def snd : labels U ⋙ E (Q := Q) ⟶ (Functor.const (A U)).obj
    (necklaceUnder.obj Q.code) where
  app P := JTTargetCommaPullback.snd W x y Q ((labels U).obj P)
  naturality {_ _} f :=
    (JTTargetCommaPullback.map_snd W x y Q ((labels U).map f)).trans (Category.comp_id _).symm

private abbrev raw := JTConeMappingPresentation.targetUnder (Raw W) (rawVertex W x) (rawVertex W y)
private def rawProjection : labels U ⋙ underDiagram W x y ⟶ (Functor.const (A U)).obj
    (raw (W := W) (x := x) (y := y)) :=
  Functor.whiskerLeft (labels U) (underCocone W x y)

private def targetMap : (Functor.const (A U)).obj (necklaceUnder.obj Q.code) ⟶
    (Functor.const (A U)).obj (raw (W := W) (x := x) (y := y)) :=
  (Functor.const (A U)).map (JTTargetCommaPullback.targetMap W x y Q)

private theorem pullbacks (P : Index U) : IsPullback ((fst U).app P) ((snd U).app P)
    ((rawProjection U).app P) ((targetMap U).app P) :=
  IsPullback.of_hasPullback ((underCocone W x y).app ((labels U).obj P))
    (JTTargetCommaPullback.targetMap W x y Q)

/-- The original natural decorated and native maps assemble into the literal pullbacks. -/
def liftNatural : cylinders U ⟶ labels U ⋙ E (Q := Q) :=
  JTPointwisePullbackLift.lift (fst U) (snd U) (rawProjection U) (targetMap U) (pullbacks U)
    (JTGraphVariableTimeTraversal.decoratedNatural U) (JTGraphVariableTimeTraversal.targetNatural U)
    (JTGraphVariableTimeTraversal.pair_square U)


/-- The full variable-source resolution maps into the original fixed-target
comma using the complete decorated and native traversals. -/
def toComma : Resolution U ⥤ TargetComma Q :=
  JTBoundaryNecklacePresentationCone.mapPresentation (E (Q := Q))
    (cylinders U) (labels U) (liftNatural U) ⋙
      (JTTargetCommaPullback.equivalence W x y Q).inverse

private abbrev obj (P : Index U) := (toNative U).obj P
private abbrev code (P : Index U) := (obj U P).left
private abbrev collapse (P : Index U) := (obj U P).hom
private abbrev time (P : Index U) := (JTGraphVariableTimeIndex.degree U).obj P

/-- The original decorated label is obtained by collapsing the native source. -/
def decoratedCollapse : labels U ⟶ (Functor.const _).obj U.left.base :=
  Functor.whiskerLeft (toNative U) (JTGraphNativeLabelDiagram.toOriginal U)

private theorem augmentation_change {P P' : Index U} (f : P ⟶ P') :
    ((cylinders U).map f).right ≫ augmentation (code U P') (time U P') =
      augmentation (code U P) (time U P) ≫ ((toNative U).map f).left.map :=
  NecklaceCylinderJointDiagram.augmentation.naturality ((joint U).map f)

/-- Collapse every parameterized cylinder to the original native source. -/
def nativeCollapse : cylinders U ⟶ (Functor.const _).obj
    (necklaceUnder.obj U.left.fiber.left) where
  app P := timeCollapse (n := time U P) (collapse U P)
  naturality {P P'} f := by
    apply Under.UnderMorphism.ext
    change ((cylinders U).map f).right ≫
        (augmentation (code U P') (time U P') ≫ (collapse U P').map) =
      (augmentation (code U P) (time U P) ≫ (collapse U P).map) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, augmentation_change U f, Category.assoc]
    exact congrArg (fun v : code U P ⟶ U.left.fiber.left ↦
      augmentation (code U P) (time U P) ≫ v.map) (Over.w ((toNative U).map f))

/-- The first projection retains the entire decorated traversal. -/
theorem lift_fst (P : Index U) : (liftNatural U).app P ≫
    JTTargetCommaPullback.fst W x y Q ((labels U).obj P) =
      (JTGraphVariableTimeTraversal.decoratedNatural U).app P :=
  JTPointwisePullbackLift.lift_fst (fst U) (snd U) (rawProjection U) (targetMap U) (pullbacks U)
    (JTGraphVariableTimeTraversal.decoratedNatural U) (JTGraphVariableTimeTraversal.targetNatural U)
    (JTGraphVariableTimeTraversal.pair_square U) P

/-- The second projection retains the specified native target map. -/
theorem lift_snd (P : Index U) : (liftNatural U).app P ≫
    JTTargetCommaPullback.snd W x y Q ((labels U).obj P) =
      (JTGraphVariableTimeTraversal.targetNatural U).app P :=
  JTPointwisePullbackLift.lift_snd (fst U) (snd U) (rawProjection U) (targetMap U) (pullbacks U)
    (JTGraphVariableTimeTraversal.decoratedNatural U) (JTGraphVariableTimeTraversal.targetNatural U)
    (JTGraphVariableTimeTraversal.pair_square U) P

private theorem decorated_collapse (P : Index U) :
    (JTGraphVariableTimeTraversal.decoratedNatural U).app P ≫
      (underDiagram W x y).map ((decoratedCollapse U).app P) =
    (nativeCollapse U).app P ≫ U.left.fiber.hom := by
  change toDecorated U (collapse U P) (fun i ↦ (family U P i).parameter) ≫
      (underDiagram W x y).map ((JTGraphNativeLabelDiagram.toOriginal U).app (obj U P)) =
    timeCollapse (n := time U P) (collapse U P) ≫ U.left.fiber.hom
  rw [JTGraphNativeLabelDiagram.toOriginal_app U (obj U P) (family U P) (family_collapse U P)]
  exact JTGraphInterpolatedCollapseOriginal.decorated_collapse
    (collapse U P) (family U P) (family_collapse U P)

private theorem native_collapse (P : Index U) :
    (JTGraphVariableTimeTraversal.targetNatural U).app P =
      (nativeCollapse U).app P ≫ necklaceUnder.map U.hom.hom := by
  apply Under.UnderMorphism.ext
  change augmentation (code U P) (time U P) ≫ (collapse U P ≫ U.hom.hom).map =
    (augmentation (code U P) (time U P) ≫ (collapse U P).map) ≫ U.hom.hom.map
  exact (Category.assoc _ _ _).symm

/-- Two composite maps into a pullback agree if the projected squares agree. -/
theorem square_of_projections {C : Type*} [Category C]
    {S X X' Y Y' B T R : C}
    {p : S ⟶ X} {a : X ⟶ X'} {b : S ⟶ Y} {q : Y ⟶ X'}
    {f : X' ⟶ B} {g : X' ⟶ T} {r : B ⟶ R} {s : T ⟶ R}
    {f₀ : X ⟶ Y'} {g₀ : X ⟶ T} {d : Y' ⟶ B}
    {v : Y ⟶ B} {w : Y ⟶ T}
    (h : IsPullback f g r s)
    (ha : a ≫ f = f₀ ≫ d) (ha' : a ≫ g = g₀)
    (hq : q ≫ f = v) (hq' : q ≫ g = w)
    (h₁ : (p ≫ f₀) ≫ d = b ≫ v) (h₂ : p ≫ g₀ = b ≫ w) :
    p ≫ a = b ≫ q := by
  apply h.hom_ext
  · rw [Category.assoc, ha, ← Category.assoc, h₁, Category.assoc, hq]
  · rw [Category.assoc, ha', h₂, Category.assoc, hq']

/-- The two collapses give the same arrow into the original fixed-target pullback. -/
theorem collapse_square (P : Index U) :
    (liftNatural U).app P ≫ (E (Q := Q)).map ((decoratedCollapse U).app P) =
      (nativeCollapse U).app P ≫
        ((JTTargetCommaPullback.toPullback W x y Q).obj U).fiber.hom := by
  let q := JTTargetCommaPullback.lift W x y Q U
  change (liftNatural U).app P ≫ (E (Q := Q)).map ((decoratedCollapse U).app P) =
    (nativeCollapse U).app P ≫ q
  have hf := JTTargetCommaPullback.map_fst W x y Q (i := (labels U).obj P)
    (j := U.left.base) ((decoratedCollapse U).app P)
  have hs := JTTargetCommaPullback.map_snd W x y Q (i := (labels U).obj P)
    (j := U.left.base) ((decoratedCollapse U).app P)
  have hp := IsPullback.of_hasPullback ((underCocone W x y).app U.left.base)
    (JTTargetCommaPullback.targetMap W x y Q)
  exact square_of_projections hp hf hs (JTTargetCommaPullback.lift_fst W x y Q U)
    (JTTargetCommaPullback.lift_snd W x y Q U)
    ((congrArg (· ≫ (underDiagram W x y).map ((decoratedCollapse U).app P))
      (lift_fst U P)).trans (decorated_collapse U P))
    ((lift_snd U P).trans (native_collapse U P))

/-- The simultaneous comparison carries its exact arrow to the original object. -/
def comparisonToOriginal : toComma U ⟶ (Functor.const (Resolution U)).obj U :=
  JTBoundaryNecklaceConeReindex.mapCone
    (JTBoundaryNecklacePresentationCone.coneFromVariableDiagram (E (Q := Q))
      ((JTTargetCommaPullback.toPullback W x y Q).obj U) (cylinders U) (labels U) (liftNatural U)
      (decoratedCollapse U) (nativeCollapse U) (collapse_square U))
    (JTTargetCommaPullback.equivalence W x y Q).inverse
    ((JTTargetCommaPullback.equivalence W x y Q).unitIso.app U).inv

/-- The full variable-source comparison in the slice of the original object. -/
def toSlice : Resolution U ⥤ Over U := Over.lift (toComma U) (comparisonToOriginal U)

/-- The simultaneous slice comparison is a Kan weak equivalence on nerves. -/
theorem toSlice_weak : WeakEquivalence (nerveMap (toSlice U)) := by
  let p := pointMap (nerve (Over U))
  haveI : WeakEquivalence p := (weakEquivalence_iff_GW _).mpr
    (DaggerNativeOverNerveWeakContractibility.point_GW U)
  apply (weakEquivalence_postcomp_iff (nerveMap (toSlice U)) p).mp
  rw [pointIsTerminal.hom_ext (nerveMap (toSlice U) ≫ p) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mpr (resolution_point_GW U)

end
end DaggerModels.PartII.JTGraphVariableTimeComparison
