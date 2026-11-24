import DaggerModelsPartII.JTHigherGraphExtensionLabels
import DaggerModelsPartII.JTFixedLiftSpaceInterleavedProjection

/-!
# Entire enlarged normalization simplices in the actual target comma
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTHigherGraphExtensionComma

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts JTMixedGraphRawRefinement
open JTOrdinaryGraphNormalizationSpace JTFixedLiftSpaceInterleaved
open JTEndpointNormalizationLifts
open JTHigherGraphExtensionLabels JTHigherInterleavedParameter JTHigherGraphPrismCylinder
open JTNecklaceEndpointCylinder JTTargetCommaPullback
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev code := MixedGraphCylinderTraversal.code
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W y)

private abbrev ls := leftSquare W ⦋d⦌ k f s x hx
private abbrev rs := rightSquare W ⦋d⦌ k f s y hy

/-- Both independent enlargement choices over the same time simplex. -/
def choices : SSet.{0} where
  obj n := leftExtension f s hx n.unop × rightExtension f s hy n.unop
  map j E := ⟨restrict (ls f s hx) j.unop E.1, restrict (rs f s hy) j.unop E.2⟩
  map_id _ := by
    funext E
    exact Prod.ext (restrict_id (ls f s hx) E.1) (restrict_id (rs f s hy) E.2)
  map_comp j j' := by
    funext E
    exact Prod.ext (restrict_comp (ls f s hx) j'.unop j.unop E.1)
      (restrict_comp (rs f s hy) j'.unop j.unop E.2)

private def leftChoice : choices f s hx hy ⟶ extensionSpace (ls f s hx) where
  app _ := Prod.fst
  naturality := by intros; rfl

private def rightChoice : choices f s hx hy ⟶ extensionSpace (rs f s hy) where
  app _ := Prod.snd
  naturality := by intros; rfl

open JTFixedLiftSpaceInterleavedProjection (projection projection_surjective)

/-- Forget the enlargements and retain the original pair of time families. -/
def forgetChoices : choices f s hx hy ⟶ space W ⦋d⦌ k f s x y hx hy :=
  prod.lift (leftChoice f s hx hy ≫ projection (ls f s hx))
    (rightChoice f s hx hy ≫ projection (rs f s hy))

/-- Every simplex of the original paired normalization space has an
enlargement in the same degree. -/
theorem forgetChoices_surjective [Fibration (endpointArrow W)] (n : SimplexCategory) :
    Function.Surjective ((forgetChoices f s hx hy).app (op n)) := by
  intro v
  let A := leftSpace W ⦋d⦌ k f s x hx
  let B := rightSpace W ⦋d⦌ k f s y hy
  let π₁ : A ⨯ B ⟶ A := prod.fst
  let π₂ : A ⨯ B ⟶ B := prod.snd
  obtain ⟨L, hL⟩ := projection_surjective (ls f s hx) n (π₁.app (op n) v)
  obtain ⟨R, hR⟩ := projection_surjective (rs f s hy) n (π₂.app (op n) v)
  refine ⟨(L, R), ?_⟩
  let v' := (forgetChoices f s hx hy).app (op n) (L, R)
  change v' = v
  apply SSet.yonedaEquiv.symm.injective
  apply prod.hom_ext
  · have h : forgetChoices f s hx hy ≫ π₁ =
        leftChoice f s hx hy ≫ projection (ls f s hx) := prod.lift_fst _ _
    have hp := congrArg (fun g : choices f s hx hy ⟶ A ↦ g.app (op n) (L, R)) h
    change π₁.app (op n) v' = (projection (ls f s hx)).app (op n) L at hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
    change π₁.app (op n) (SSet.yonedaEquiv (SSet.yonedaEquiv.symm v')) =
      π₁.app (op n) (SSet.yonedaEquiv (SSet.yonedaEquiv.symm v))
    rw [SSet.yonedaEquiv.apply_symm_apply, SSet.yonedaEquiv.apply_symm_apply]
    exact hp.trans hL
  · have h : forgetChoices f s hx hy ≫ π₂ =
        rightChoice f s hx hy ≫ projection (rs f s hy) := prod.lift_snd _ _
    have hp := congrArg (fun g : choices f s hx hy ⟶ B ↦ g.app (op n) (L, R)) h
    change π₂.app (op n) v' = (projection (rs f s hy)).app (op n) R at hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
    change π₂.app (op n) (SSet.yonedaEquiv (SSet.yonedaEquiv.symm v')) =
      π₂.app (op n) (SSet.yonedaEquiv (SSet.yonedaEquiv.symm v))
    rw [SSet.yonedaEquiv.apply_symm_apply, SSet.yonedaEquiv.apply_symm_apply]
    exact hp.trans hR

abbrev Index := (choices f s hx hy).Elementsᵒᵖ

/-- Keep the exact time simplex and its original operator. -/
def time : Index f s hx hy ⥤ SimplexCategory :=
  (CategoryOfElements.π (choices f s hx hy)).leftOp

private abbrev nOf (i : Index f s hx hy) := (time f s hx hy).obj i
private abbrev L (i : Index f s hx hy) : leftExtension f s hx (nOf f s hx hy i) := i.unop.2.1
private abbrev R (i : Index f s hx hy) : rightExtension f s hy (nOf f s hx hy i) := i.unop.2.2

private abbrev zOf (i : Index f s hx hy) :=
  label f s hx hy (L f s hx hy i) (R f s hx hy i)

private abbrev TIdx := DecoratedNecklaceHomDiagram.Index W x y
private abbrev lbl (i : Index f s hx hy) : TIdx (W := W) (x := x) (y := y) :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (code d) (common k (nOf f s hx hy i))
    (zOf f s hx hy i)

/-- Restriction of the original full label along a paired extension operator. -/
theorem z_map {i j : Index f s hx hy} (u : i ⟶ j) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).map
        (mapTime k ((time f s hx hy).map u)).op (zOf f s hx hy j) = zOf f s hx hy i := by
  let a := (time f s hx hy).map u
  have h := label_mapTime f s hx hy a (L f s hx hy j) (R f s hx hy j)
  have hv : (choices f s hx hy).map a.op j.unop.2 = i.unop.2 := u.unop.property
  change _ = label f s hx hy ((choices f s hx hy).map a.op j.unop.2).1
    ((choices f s hx hy).map a.op j.unop.2).2 at h
  rw [hv] at h
  exact h

private def labelArrow {i j : Index f s hx hy} (u : i ⟶ j) :
    lbl f s hx hy i ⟶ lbl f s hx hy j := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let a := (time f s hx hy).map u
  let g : (code d, common k (nOf f s hx hy i)) ⟶ (code d, common k (nOf f s hx hy j)) :=
    (𝟙 (code d), mapTime k a)
  refine (CategoryOfElements.homMk
    (P.elementsMk (op (code d, common k (nOf f s hx hy j))) (zOf f s hx hy j))
    (P.elementsMk (op (code d, common k (nOf f s hx hy i))) (zOf f s hx hy i))
    g.op ?_).op
  let F := orderedNecklaceLabels W (boundaryPoint W x y)
  change (F.obj (op (code d))).map (mapTime k a).op
      ((F.map (𝟙 (op (code d)))).app (op (common k (nOf f s hx hy j))) (zOf f s hx hy j)) =
    zOf f s hx hy i
  rw [F.map_id]
  exact z_map f s hx hy u

private abbrev labelProjection :=
  OrderedLabelElements.projection W (boundaryPoint W x y)

/-- The ordered labels of all choices and all time operators in the
original decorated index. -/
def toLabels : Index f s hx hy ⥤ TIdx (W := W) (x := x) (y := y) where
  obj := lbl f s hx hy
  map := labelArrow f s hx hy
  map_id i := by
    letI : (labelProjection (W := W) (x := x) (y := y)).Faithful := by
      change ((CategoryOfElements.π
        (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y))).leftOp).Faithful
      infer_instance
    apply (labelProjection (W := W) (x := x) (y := y)).map_injective
    change (𝟙 (code d), mapTime k ((time f s hx hy).map (𝟙 i))) =
      (𝟙 (code d), 𝟙 (common k (nOf f s hx hy i)))
    rw [(time f s hx hy).map_id, mapTime_id]
  map_comp u v := by
    letI : (labelProjection (W := W) (x := x) (y := y)).Faithful := by
      change ((CategoryOfElements.π
        (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y))).leftOp).Faithful
      infer_instance
    apply (labelProjection (W := W) (x := x) (y := y)).map_injective
    rw [Functor.map_comp]
    change (𝟙 (code d), mapTime k ((time f s hx hy).map (u ≫ v))) =
      (𝟙 (code d) ≫ 𝟙 (code d),
        mapTime k ((time f s hx hy).map u) ≫ mapTime k ((time f s hx hy).map v))
    rw [(time f s hx hy).map_comp, mapTime_comp, Category.id_comp]

/-- Each time simplex has its actual reduced cylinder as source. -/
def sourceDiagram : Index f s hx hy ⥤ Under JTXiEndpointCollapse.boundary :=
  time f s hx hy ⋙ under (code d)

variable {q : (single d).toSSet ⟶ Raw W}
variable (hq : nativeRawGraph W d k f s = q)
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)

private abbrev target := (⟨single d, q, qx, qy⟩ : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
private abbrev D := JTTargetCommaPullback.diagram W x y (target qx qy)

private abbrev eOf (i : Index f s hx hy) :=
  families f s hx hy (L f s hx hy i) (R f s hx hy i) 0

include hq qx qy in
private theorem rawEquation (i : Index f s hx hy) :
    cylinderMap (code d) (nativeGraphParameter s) (nOf f s hx hy i) ≫
        descend W x y (code d) (common k (nOf f s hx hy i)) (zOf f s hx hy i) =
      NecklaceCylinderAugmentation.augmentation (code d) (nOf f s hx hy i) ≫
        (MixedGraphCylinderTraversal.collapseOuter d).map ≫ q :=
  JTHigherMixedGraphTargetLift.whole_raw f s hq qx qy (eOf f s hx hy i)
    (left_vertical f s hx (L f s hx hy i)) (right_vertical f s hy (R f s hx hy i))

private def liftAt (i : Index f s hx hy) :
    (sourceDiagram f s hx hy).obj i ⟶ (D qx qy).obj ((toLabels f s hx hy).obj i) :=
  JTHigherMixedGraphTargetLift.lift f s qx qy (eOf f s hx hy i)
    (rawEquation f s hx hy hq qx qy i)

private theorem liftAt_fst (i : Index f s hx hy) :
    liftAt f s hx hy hq qx qy i ≫ JTTargetCommaPullback.fst W x y (target qx qy) (lbl f s hx hy i) =
      JTHigherMixedGraphTargetLift.toDecorated d s (nOf f s hx hy i) :=
  JTHigherMixedGraphTargetLift.lift_decorated f s qx qy (eOf f s hx hy i)
    (rawEquation f s hx hy hq qx qy i)

private theorem liftAt_snd (i : Index f s hx hy) :
    liftAt f s hx hy hq qx qy i ≫ JTTargetCommaPullback.snd W x y (target qx qy) (lbl f s hx hy i) =
      JTHigherMixedGraphTargetLift.toNativeTarget d (nOf f s hx hy i) :=
  JTHigherMixedGraphTargetLift.lift_native f s qx qy (eOf f s hx hy i)
    (rawEquation f s hx hy hq qx qy i)

private theorem under_map {i j : Index f s hx hy} (u : i ⟶ j) :
    (underDiagram W x y).map ((toLabels f s hx hy).map u) =
      (under (code d)).map (mapTime k ((time f s hx hy).map u)) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 (code d)) (common k (nOf f s hx hy i)) ≫
    (value (code d)).map (mapTime k ((time f s hx hy).map u)) = _
  rw [nativeMap_id, Category.id_comp]
  rfl

/-- The actual comparison into the fixed-target pullbacks is natural in
all enlargement time operators and retains both full projections. -/
def liftNatural :
    sourceDiagram f s hx hy ⟶ toLabels f s hx hy ⋙ D qx qy where
  app := liftAt f s hx hy hq qx qy
  naturality {i j} u := by
    let a := (time f s hx hy).map u
    change (under (code d)).map a ≫ liftAt f s hx hy hq qx qy j =
      liftAt f s hx hy hq qx qy i ≫ (D qx qy).map ((toLabels f s hx hy).map u)
    let v : lbl f s hx hy i ⟶ lbl f s hx hy j := (toLabels f s hx hy).map u
    apply pullback.hom_ext (f := (underCocone W x y).app (lbl f s hx hy j))
      (g := targetMap W x y (target qx qy))
    · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y (target qx qy) (lbl f s hx hy j) =
        (_ ≫ (D qx qy).map v) ≫ JTTargetCommaPullback.fst W x y (target qx qy) (lbl f s hx hy j)
      rw [Category.assoc, liftAt_fst f s hx hy hq qx qy j, Category.assoc,
        map_fst W x y (target qx qy) v, ← Category.assoc,
        liftAt_fst f s hx hy hq qx qy i, under_map f s hx hy u]
      apply Under.UnderMorphism.ext
      exact (cylinderMap_mapTime (code d) (nativeGraphParameter s) a).symm
    · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y (target qx qy) (lbl f s hx hy j) =
        (_ ≫ (D qx qy).map v) ≫ JTTargetCommaPullback.snd W x y (target qx qy) (lbl f s hx hy j)
      rw [Category.assoc, liftAt_snd f s hx hy hq qx qy j, Category.assoc,
        map_snd W x y (target qx qy) v, liftAt_snd f s hx hy hq qx qy i]
      exact JTHigherMixedGraphTargetLift.toNativeTarget_natural d a

/-- All native necklaces in the enlarged time cylinders map functorially
to the original fixed-target pullback presentation. -/
def toPullbackPresentation :
    BoundaryNecklaceComma.Presentation (sourceDiagram f s hx hy) ⥤
      JTTargetCommaPullback.Presentation W x y (target qx qy) :=
  Grothendieck.map (Functor.whiskerRight (liftNatural f s hx hy hq qx qy)
    BoundaryNecklaceComma.diagram) ⋙
      Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram (D qx qy)) (toLabels f s hx hy)

/-- The same simultaneous comparisons land in the original target comma. -/
def toComma :
    BoundaryNecklaceComma.Presentation (sourceDiagram f s hx hy) ⥤
      CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) (target qx qy) :=
  toPullbackPresentation f s hx hy hq qx qy ⋙
    (JTTargetCommaPullback.equivalence W x y (target qx qy)).inverse

end

end DaggerModels.PartII.JTHigherGraphExtensionComma
