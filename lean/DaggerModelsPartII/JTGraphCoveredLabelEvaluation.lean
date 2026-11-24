import DaggerModelsPartII.JTActualJointChainLabels
import DaggerModelsPartII.JTEndpointReducedPullbackCover
import DaggerModelsPartII.JTDecoratedIntervalCylinder

/-! Evaluate a graph-covered native cylinder in the unchanged fixed-target comma. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphCoveredLabelEvaluation

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (codes)
open JTNecklaceEndpointCylinder (cylinder endpointInclusion descend_cylinder)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open JTEndpointReducedPullbackCover (boundaryInclusion boundaryProjection collapse)
open NecklaceCylinderAugmentation (augmentation_cylinder)
open JTTargetIntervalOverMapping (whole)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (time : I ⥤ SimplexCategory)
variable (c : codes L ⟶ (Functor.const I).obj Q.code)

private abbrev D := Over.lift (codes L) c
private abbrev T (p : I) := ((D Q L c).obj p).left
private abbrev product :=
  JTJointRelativeParameters.withTime Q.map J time (D Q L c) (whole Q.code)
private abbrev cylinders :=
  JTDecoratedIntervalCylinder.reduced Q (D Q L c) time
private abbrev degree :=
  L ⋙ OrderedLabelElements.projection W (boundaryPoint W x y) ⋙
    CategoryTheory.Prod.snd NecklaceCode SimplexCategory
private abbrev bTime := time ⋙ JTXiEndpointCollapse.boundaryCylinder
private abbrev e := Functor.whiskerLeft time JTXiEndpointCollapse.cylinderProjection

/-- The literal endpoint inclusion of the original native product cylinder. -/
def boundary : bTime time ⟶ product Q L time c where
  app p := endpointInclusion (T Q L c p) ⊗ₘ 𝟙 (J.obj (time.obj p))
  naturality {p p'} f := by
    change (𝟙 B ⊗ₘ J.map (time.map f)) ≫
        (endpointInclusion (T Q L c p') ⊗ₘ 𝟙 (J.obj (time.obj p'))) =
      (endpointInclusion (T Q L c p) ⊗ₘ 𝟙 (J.obj (time.obj p))) ≫
        ((JTDecoratedIntervalDiagram.parameterize Q.map J time
          (D Q L c ⋙ whole Q.code)).map f).left
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id, Category.id_comp]
    change endpointInclusion (T Q L c p') ⊗ₘ J.map (time.map f) =
      (endpointInclusion (T Q L c p) ≫ ((D Q L c).map f).left.map) ⊗ₘ
        J.map (time.map f)
    exact congrArg (fun a ↦ a ⊗ₘ J.map (time.map f))
      (JTNecklaceEndpointCylinder.endpointInclusion_natural ((D Q L c).map f).left).symm

variable {Y : I ⥤ SSet.{0}} (π : Y ⟶ product Q L time c)
variable (θ : Y ⟶ degree (W := W) (x := x) (y := y) L ⋙ J)
variable (hraw : ∀ p, lift (π.app p ≫ fst _ _) (θ.app p) ≫
    JTNecklaceLabelRealization.realizedLabel (T Q L c p).toSSet W
      ((degree (W := W) (x := x) (y := y) L).obj p)
      (JTRealizedLabelEndpoints.orderedLabel W x y (T Q L c p)
        ((degree (W := W) (x := x) (y := y) L).obj p)
        (OrderedLabelElements.label W (boundaryPoint W x y) (L.obj p))) =
    (π.app p ≫ fst _ _) ≫ ((D Q L c).obj p).hom.map ≫ Q.map)

private abbrev u := boundaryInclusion π (boundary Q L time c)
private abbrev v := boundaryProjection π (boundary Q L time c)
private abbrev ec := collapse π (boundary Q L time c) (e time)

/-- Collapse the entire inverse image of the two endpoint lines. -/
abbrev reduced := JTEndpointReducedPullbackCover.reduced
  π (boundary Q L time c) (e time)

private def cylinderLeg :
    product Q L time c ⟶ cylinders Q L time c ⋙ Under.forget B where
  app p := (cylinder (T Q L c p)).app (time.obj p)
  naturality _ _ f :=
    (JTDecoratedIntervalCylinder.reduced_map_cylinder Q (D Q L c) time f).symm

private theorem old_boundary :
    boundary Q L time c ≫ cylinderLeg Q L time c =
      e time ≫ JTEndpointReducedCover.boundary (cylinders Q L time c) := by
  apply NatTrans.ext
  funext p
  exact (JTNecklaceEndpointCylinder.isPushout (T Q L c p) (time.obj p)).w

/-- Recover the original reduced cylinder under its endpoints. -/
def projection : reduced Q L time c π ⟶ cylinders Q L time c :=
  JTEndpointReducedPullbackCover.projection π (boundary Q L time c) (e time)
    (cylinders Q L time c) (cylinderLeg Q L time c) (old_boundary Q L time c)

/-- Weakness of the reduced projection over a positive-length native target. -/
theorem projection_weak (hQ : 0 < Q.code.len) (p : I)
    (hπ : trivialFibrations SSet.{0} (π.app p)) :
    WeakEquivalence ((projection Q L time c π).app p).right := by
  haveI : Mono (endpointInclusion Q.code) :=
    NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos Q.code hQ
  have hn : endpointInclusion (T Q L c p) ≫ ((D Q L c).obj p).hom.map =
      endpointInclusion Q.code :=
    JTNecklaceEndpointCylinder.endpointInclusion_natural ((D Q L c).obj p).hom
  haveI : Mono (endpointInclusion (T Q L c p)) := mono_of_mono_fac hn
  haveI : Mono ((boundary Q L time c).app p) := by
    change Mono (endpointInclusion (T Q L c p) ⊗ₘ 𝟙 (J.obj (time.obj p)))
    rw [tensorHom_id]
    exact DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono _ _
  exact JTEndpointReducedPullbackCover.projection_weak π (boundary Q L time c) (e time)
    (cylinders Q L time c) (cylinderLeg Q L time c) (old_boundary Q L time c) p
    (JTNecklaceEndpointCylinder.isPushout (T Q L c p) (time.obj p)) hπ



/-- Weakness only requires a monic source endpoint boundary; the fixed target
may be a point when the source itself contains a nondegenerate added edge. -/
theorem projection_weak_of_native_mono (p : I)
    [Mono (endpointInclusion ((codes L).obj p))]
    (hπ : trivialFibrations SSet.{0} (π.app p)) :
    WeakEquivalence ((projection Q L time c π).app p).right := by
  haveI : Mono (endpointInclusion (T Q L c p)) := by
    change Mono (endpointInclusion ((codes L).obj p))
    infer_instance
  haveI : Mono ((boundary Q L time c).app p) := by
    change Mono (endpointInclusion (T Q L c p) ⊗ₘ 𝟙 (J.obj (time.obj p)))
    rw [tensorHom_id]
    exact DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono _ _
  exact JTEndpointReducedPullbackCover.projection_weak π (boundary Q L time c) (e time)
    (cylinders Q L time c) (cylinderLeg Q L time c) (old_boundary Q L time c) p
    (JTNecklaceEndpointCylinder.isPushout (T Q L c p) (time.obj p)) hπ

private abbrev horizontal (p : I) :=
  π.app p ≫ fst (T Q L c p).toSSet (J.obj (time.obj p))

private def graphProduct : Y ⟶
    JTJointRelativeParameters.withTime Q.map J
      (degree (W := W) (x := x) (y := y) L) (D Q L c) (whole Q.code) where
  app p := lift (horizontal Q L time c π p) (θ.app p)
  naturality {p q} f := by
    change _ = _ ≫ ((JTDecoratedIntervalDiagram.parameterize Q.map J
      (degree (W := W) (x := x) (y := y) L)
      (D Q L c ⋙ whole Q.code)).map f).left
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      let a := Y.map f
      let g := ((D Q L c).map f).left.map
      let n := time.map f
      let p₀ := π.app p
      let p₁ := π.app q
      have hπ : a ≫ p₁ = p₀ ≫ (product Q L time c).map f :=
        π.naturality f
      have hfst : (product Q L time c).map f ≫
          fst (T Q L c q).toSSet (J.obj (time.obj q)) =
        fst (T Q L c p).toSSet (J.obj (time.obj p)) ≫ g := by
        change ((JTDecoratedIntervalDiagram.parameterize Q.map J time
          (D Q L c ⋙ whole Q.code)).map f).left ≫ _ = _
        rw [JTDecoratedIntervalDiagram.parameterize_map_left]
        exact tensorHom_fst g (J.map n)
      let v := fst (T Q L c q).toSSet (J.obj (time.obj q))
      let u₀ := fst (T Q L c p).toSSet (J.obj (time.obj p))
      change a ≫ p₁ ≫ v = (p₀ ≫ u₀) ≫ g
      calc
        _ = p₀ ≫ (product Q L time c).map f ≫ v := by
          rw [← Category.assoc a, hπ, Category.assoc p₀]
        _ = p₀ ≫ u₀ ≫ g := congrArg (p₀ ≫ ·) hfst
        _ = _ := (Category.assoc _ _ _).symm
    · simp only [Category.assoc, lift_snd]
      change Y.map f ≫ θ.app q =
        θ.app p ≫ J.map ((degree (W := W) (x := x) (y := y) L).map f)
      exact θ.naturality f

private abbrev target :=
  L ⋙ underDiagram W x y

private abbrev graphLeg : Y ⟶
    JTDecoratedIntervalCylinder.reduced Q (D Q L c)
      (degree (W := W) (x := x) (y := y) L) ⋙ Under.forget B :=
  graphProduct Q L time c π θ ≫
    cylinderLeg Q L (degree (W := W) (x := x) (y := y) L) c

private theorem graph_boundary : u Q L time c π ≫ graphLeg Q L time c π θ =
    ec Q L time c π ≫
      JTEndpointReducedCover.boundary
        (JTDecoratedIntervalCylinder.reduced Q (D Q L c)
          (degree (W := W) (x := x) (y := y) L)) := by
  apply NatTrans.ext
  funext p
  let θ₀ := θ.app p
  let k := (degree (W := W) (x := x) (y := y) L).obj p
  let n := time.obj p
  let h := (u Q L time c π).app p
  let j := (v Q L time c π).app p
  have hs : h ≫ π.app p = j ≫ (boundary Q L time c).app p :=
    NatTrans.congr_app (JTEndpointReducedPullbackCover.boundary_square π
      (boundary Q L time c)) p
  change h ≫ lift (π.app p ≫ fst (T Q L c p).toSSet (J.obj n)) θ₀ ≫
      (cylinder (T Q L c p)).app k =
    (j ≫ fst B (J.obj n)) ≫ (JTNecklaceEndpointCylinder.boundary
      (T Q L c p)).app k
  have hd : (boundary Q L time c).app p ≫
      fst (T Q L c p).toSSet (J.obj n) =
      fst B (J.obj n) ≫ endpointInclusion (T Q L c p) :=
    tensorHom_fst (endpointInclusion (T Q L c p)) (𝟙 (J.obj n))
  rw [← Category.assoc h, comp_lift, ← Category.assoc h, hs, Category.assoc j, hd,
    ← Category.assoc j]
  exact JTNecklaceCylinderConnector.boundary_collapse (T Q L c p) k
    (j ≫ fst B (J.obj n)) (h ≫ θ₀)

/-- The decorated cylinder map descends through the complete covered boundary. -/
def decorated : reduced Q L time c π ⟶ target (W := W) (x := x) (y := y) L :=
  JTEndpointReducedCover.descend (u Q L time c π) (ec Q L time c π)
    (JTDecoratedIntervalCylinder.reduced Q (D Q L c)
      (degree (W := W) (x := x) (y := y) L))
    (graphLeg Q L time c π θ) (graph_boundary Q L time c π θ)

/-- The native target leg uses the original necklace quotient. -/
def nativeLeg : reduced Q L time c π ⟶
    (Functor.const I).obj (BoundaryNecklaceComma.necklaceUnder.obj Q.code) :=
  projection Q L time c π ≫ JTDecoratedIntervalCylinder.native Q (D Q L c) time

private abbrev inc := pushout.inl (u Q L time c π) (ec Q L time c π)

private theorem projection_cylinder (p : I) :
    (inc Q L time c π).app p ≫ ((projection Q L time c π).app p).right =
      π.app p ≫ (cylinderLeg Q L time c).app p :=
  JTEndpointReducedPullbackCover.projection_cylinder π (boundary Q L time c) (e time)
    (cylinders Q L time c) (cylinderLeg Q L time c) (old_boundary Q L time c) p

private theorem decorated_cylinder (p : I) :
    (inc Q L time c π).app p ≫ ((decorated Q L time c π θ).app p).right =
      (graphLeg Q L time c π θ).app p :=
  JTEndpointReducedCover.descend_cylinder (u Q L time c π) (ec Q L time c π)
    (JTDecoratedIntervalCylinder.reduced Q (D Q L c)
      (degree (W := W) (x := x) (y := y) L))
    (graphLeg Q L time c π θ) (graph_boundary Q L time c π θ) p



include hraw in
/-- Decorated and native maps have the same literal fixed raw target. -/
theorem raw_square (p : I) :
    (decorated Q L time c π θ).app p ≫ (underCocone W x y).app (L.obj p) =
      (nativeLeg Q L time c π).app p ≫ JTTargetCommaPullback.targetMap W x y Q := by
  let l := (decorated Q L time c π θ).app p ≫ (underCocone W x y).app (L.obj p)
  let r := (nativeLeg Q L time c π).app p ≫ JTTargetCommaPullback.targetMap W x y Q
  change l = r
  apply Under.UnderMorphism.ext
  apply ((IsPushout.of_hasPushout (u Q L time c π) (ec Q L time c π)).map
    ((CategoryTheory.evaluation I SSet.{0}).obj p)).hom_ext
  · change (inc Q L time c π).app p ≫ ((decorated Q L time c π θ).app p).right ≫
        ((underCocone W x y).app (L.obj p)).right =
      (inc Q L time c π).app p ≫ ((projection Q L time c π).app p).right ≫
        (NecklaceCylinderAugmentation.augmentation (T Q L c p) (time.obj p) ≫
          ((D Q L c).obj p).hom.map) ≫ Q.map
    rw [← Category.assoc ((inc Q L time c π).app p), decorated_cylinder,
      ← Category.assoc ((inc Q L time c π).app p), projection_cylinder]
    change (lift (horizontal Q L time c π p) (θ.app p) ≫
        (cylinder (T Q L c p)).app ((degree (W := W) (x := x) (y := y) L).obj p)) ≫
          ((underCocone W x y).app (L.obj p)).right =
      (π.app p ≫ (cylinder (T Q L c p)).app (time.obj p)) ≫
        (NecklaceCylinderAugmentation.augmentation (T Q L c p) (time.obj p) ≫
          ((D Q L c).obj p).hom.map) ≫ Q.map
    simp only [Category.assoc]
    rw [← Category.assoc ((cylinder (T Q L c p)).app (time.obj p))
      (NecklaceCylinderAugmentation.augmentation (T Q L c p) (time.obj p)),
      augmentation_cylinder]
    change lift (horizontal Q L time c π p) (θ.app p) ≫
        (cylinder (T Q L c p)).app ((degree (W := W) (x := x) (y := y) L).obj p) ≫
          JTNecklaceEndpointCylinder.descend W x y (T Q L c p)
            ((degree (W := W) (x := x) (y := y) L).obj p)
              (OrderedLabelElements.label W (boundaryPoint W x y) (L.obj p)) = _
    rw [descend_cylinder]
    exact (hraw p).trans (Category.assoc _ _ _)
  · exact (Under.w l).trans (Under.w r).symm

include hraw in
/-- Every internal necklace in the covered reduced cylinder evaluates in the
unchanged fixed-target comma category. -/
def evaluation :
    BoundaryNecklaceComma.Presentation (reduced Q L time c π) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  JTDecoratedIntervalCylinder.evaluateFromProjections Q L (reduced Q L time c π)
    (decorated Q L time c π θ) (nativeLeg Q L time c π)
    (raw_square Q L time c π θ hraw)


end
end DaggerModels.PartII.JTGraphCoveredLabelEvaluation
