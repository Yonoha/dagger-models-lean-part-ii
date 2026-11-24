import DaggerModelsPartII.JTOrderedLabelPaddingPrismChainGraphs
import DaggerModelsPartII.JTOrderedLabelPaddingPrismChainLabels
import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange
import DaggerModelsPartII.FullInverseImagePrism
import DaggerModelsPartII.JTNecklaceCylinderConnector
import DaggerModelsPartII.JTDecoratedIntervalCylinder
import DaggerModelsPartII.JTVariablePresentationCone

/-! Evaluate the entire reduced covered chain cylinder in the original fixed-target comma. -/

set_option autoImplicit false
set_option maxHeartbeats 500000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismChainCylinder

open JTOrderedLabelPaddingPrismChains (base oldLabels realizedLabels chainLabels
  chainToOriginal chainToRealized chainToOriginal_projection chainToRealized_projection
  ordinals toOriginal toRealized)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family)
open JTOrderedLabelPaddingPrismChainGraphs (graphCover original realizedParameter horizontal)
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

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time)

private abbrev b := boundaryPoint W x y
private abbrev I := JTOrderedLabelPaddingPrismChains.Index W (b (W := W) (x := x) (y := y)) L
private abbrev oldTime :=
  base W (b (W := W) (x := x) (y := y)) L ⋙
    JTOrderedLabelPaddingPrismSliceArrow.originalBase W (b (W := W) (x := x) (y := y)) L ⋙ time
private abbrev displayed := realizedLabels W (b (W := W) (x := x) (y := y)) L
private abbrev degree := displayed (L := L) ⋙
  OrderedLabelElements.projection W (b (W := W) (x := x) (y := y)) ⋙
    CategoryTheory.Prod.snd NecklaceCode SimplexCategory
private abbrev D := JTJointRelativeGraphFamily.native (original F)
private abbrev T (p : I (L := L)) := ((D F).obj p).left
private abbrev product (v : I (L := L) ⥤ SimplexCategory) :=
  JTJointRelativeParameters.withTime Q.map J v (D F) (whole Q.code)
private abbrev cylinders (v : I (L := L) ⥤ SimplexCategory) :=
  JTDecoratedIntervalCylinder.reduced Q (D F) v
private abbrev π := JTOrderedLabelPaddingPrismChainGraphs.projection F
private abbrev d := JTJointRelativeGraphFamily.productBoundary (original F)
private abbrev e := Functor.whiskerLeft (oldTime (L := L) (time := time))
  JTXiEndpointCollapse.cylinderProjection
private abbrev u := boundaryInclusion (π F) (d F)
private abbrev v := boundaryProjection (π F) (d F)
private abbrev ec := collapse (π F) (d F) (e (time := time))

/-- The graph covered by the chain choices, with both lifted endpoints collapsed. -/
abbrev reduced := JTEndpointReducedPullbackCover.reduced (π F) (d F) (e (time := time))

private def cylinderLeg (s : I (L := L) ⥤ SimplexCategory) :
    product F s ⟶ cylinders F s ⋙ Under.forget B where
  app p := (cylinder (T F p)).app (s.obj p)
  naturality _ _ f :=
    (JTDecoratedIntervalCylinder.reduced_map_cylinder Q (D F) s f).symm

private theorem old_boundary :
    d F ≫ cylinderLeg F (oldTime (time := time)) =
      e (time := time) ≫ JTEndpointReducedCover.boundary (cylinders F (oldTime (time := time))) := by
  apply NatTrans.ext
  funext p
  exact (JTNecklaceEndpointCylinder.isPushout (T F p) ((oldTime (time := time)).obj p)).w

/-- The projection under both ordered endpoints to the exact old cylinder. -/
def projection : reduced F ⟶ cylinders F (oldTime (time := time)) :=
  JTEndpointReducedPullbackCover.projection (π F) (d F) (e (time := time))
    (cylinders F (oldTime (time := time))) (cylinderLeg F _) (old_boundary F)

/-- The reduced projection is weak in each component over a positive-length target. -/
theorem projection_weak (hQ : 0 < Q.code.len) (p : I (L := L)) :
    WeakEquivalence ((projection F).app p).right := by
  haveI : Mono (endpointInclusion Q.code) :=
    NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos Q.code hQ
  have hn : endpointInclusion (T F p) ≫ ((original F).collapse.app p).map =
      endpointInclusion Q.code :=
    JTNecklaceEndpointCylinder.endpointInclusion_natural ((original F).collapse.app p)
  haveI : Mono (endpointInclusion (T F p)) := mono_of_mono_fac hn
  haveI : Mono ((d F).app p) := by
    change Mono (endpointInclusion (T F p) ⊗ₘ 𝟙 (J.obj ((oldTime (time := time)).obj p)))
    rw [tensorHom_id]
    exact DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono _ _
  exact JTEndpointReducedPullbackCover.projection_weak (π F) (d F) (e (time := time))
    (cylinders F (oldTime (time := time))) (cylinderLeg F _) (old_boundary F) p
    (JTNecklaceEndpointCylinder.isPushout (T F p) ((oldTime (time := time)).obj p))
    (JTOrderedLabelPaddingPrismChainGraphs.projection_trivialFibration F p)

private def graphProduct (s : I (L := L) ⥤ SimplexCategory)
    (θ : graphCover F ⟶ s ⋙ J) : graphCover F ⟶ product F s where
  app p := lift (horizontal F p) (θ.app p)
  naturality {p q} f := by
    change _ = _ ≫ ((JTDecoratedIntervalDiagram.parameterize Q.map J s
      (D F ⋙ whole Q.code)).map f).left
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      let a := (graphCover F).map f
      let g := ((D F).map f).left.map
      let n := (oldTime (time := time)).map f
      let p₀ := (π F).app p
      let p₁ := (π F).app q
      have hπ : a ≫ p₁ = p₀ ≫ (JTOrderedLabelPaddingPrismChainGraphs.X F).map f :=
        (π F).naturality f
      have hfst : (JTOrderedLabelPaddingPrismChainGraphs.X F).map f ≫
          fst (T F q).toSSet (J.obj ((oldTime (time := time)).obj q)) =
        fst (T F p).toSSet (J.obj ((oldTime (time := time)).obj p)) ≫ g := by
        change ((JTDecoratedIntervalDiagram.parameterize Q.map J (oldTime (time := time))
          (D F ⋙ whole Q.code)).map f).left ≫ _ = _
        rw [JTDecoratedIntervalDiagram.parameterize_map_left]
        exact tensorHom_fst g (J.map n)
      let v := fst (T F q).toSSet (J.obj ((oldTime (time := time)).obj q))
      let u₀ := fst (T F p).toSSet (J.obj ((oldTime (time := time)).obj p))
      change a ≫ p₁ ≫ v = (p₀ ≫ u₀) ≫ g
      calc
        _ = p₀ ≫ (JTOrderedLabelPaddingPrismChainGraphs.X F).map f ≫ v := by
          rw [← Category.assoc a, hπ, Category.assoc p₀]
        _ = p₀ ≫ u₀ ≫ g := congrArg (p₀ ≫ ·) hfst
        _ = _ := (Category.assoc _ _ _).symm
    · simp only [Category.assoc, lift_snd]
      change (graphCover F).map f ≫ θ.app q = θ.app p ≫ J.map (s.map f)
      exact θ.naturality f

private abbrev target := displayed (L := L) ⋙ underDiagram W x y

private abbrev graphLeg (s : I (L := L) ⥤ SimplexCategory)
    (θ : graphCover F ⟶ s ⋙ J) : graphCover F ⟶ cylinders F s ⋙ Under.forget B :=
  graphProduct F s θ ≫ cylinderLeg F s

private theorem graph_boundary (s : I (L := L) ⥤ SimplexCategory)
    (θ : graphCover F ⟶ s ⋙ J) : u F ≫ graphLeg F s θ =
      ec F ≫ JTEndpointReducedCover.boundary (cylinders F s) := by
  apply NatTrans.ext
  funext p
  let θ₀ := θ.app p
  let k := s.obj p
  let n := (oldTime (time := time)).obj p
  let h := (u F).app p
  let j := (v F).app p
  have hs : h ≫ (π F).app p = j ≫ (d F).app p :=
    NatTrans.congr_app (JTEndpointReducedPullbackCover.boundary_square (π F) (d F)) p
  change h ≫ lift ((π F).app p ≫ fst (T F p).toSSet (J.obj n)) θ₀ ≫
      (cylinder (T F p)).app k =
    (j ≫ fst B (J.obj n)) ≫ (JTNecklaceEndpointCylinder.boundary (T F p)).app k
  have hd : (d F).app p ≫ fst (T F p).toSSet (J.obj n) =
      fst B (J.obj n) ≫ endpointInclusion (T F p) :=
    tensorHom_fst (endpointInclusion (T F p)) (𝟙 (J.obj n))
  rw [← Category.assoc h, comp_lift, ← Category.assoc h, hs, Category.assoc j, hd,
    ← Category.assoc j]
  exact JTNecklaceCylinderConnector.boundary_collapse (T F p) k
    (j ≫ fst B (J.obj n)) (h ≫ θ₀)

private def descendParameter (s : I (L := L) ⥤ SimplexCategory)
    (θ : graphCover F ⟶ s ⋙ J) : reduced F ⟶ cylinders F s :=
  JTEndpointReducedCover.descend (u F) (ec F) (cylinders F s)
    (graphLeg F s θ) (graph_boundary F s θ)

/-- The realized decorated map includes all coefficient choices and descends under both endpoints. -/
def decorated : reduced F ⟶ target (L := L) :=
  descendParameter F degree (realizedParameter F)

/-- The native target leg is transported through the exact original projection. -/
def nativeLeg : reduced F ⟶
    (Functor.const (I (L := L))).obj (BoundaryNecklaceComma.necklaceUnder.obj Q.code) :=
  projection F ≫ JTDecoratedIntervalCylinder.native Q (D F) (oldTime (time := time))

private abbrev inc := pushout.inl (u F) (ec F)

private theorem projection_cylinder (p : I (L := L)) :
    (inc F).app p ≫ ((projection F).app p).right =
      (π F).app p ≫ (cylinderLeg F (oldTime (time := time))).app p :=
  JTEndpointReducedPullbackCover.projection_cylinder (π F) (d F) (e (time := time))
    (cylinders F (oldTime (time := time))) (cylinderLeg F _) (old_boundary F) p

private theorem parameter_cylinder (s : I (L := L) ⥤ SimplexCategory)
    (θ : graphCover F ⟶ s ⋙ J) (p : I (L := L)) :
    (inc F).app p ≫ ((descendParameter F s θ).app p).right = (graphLeg F s θ).app p :=
  JTEndpointReducedCover.descend_cylinder (u F) (ec F) (cylinders F s)
    (graphLeg F s θ) (graph_boundary F s θ) p

private theorem decorated_cylinder (p : I (L := L)) :
    (inc F).app p ≫ ((decorated F).app p).right =
      (graphLeg F degree (realizedParameter F)).app p :=
  parameter_cylinder F degree (realizedParameter F) p

/-- The realized decorated and original native legs have literally the same fixed raw target. -/
theorem raw_square (p : I (L := L)) :
    (decorated F).app p ≫ (underCocone W x y).app (displayed.obj p) =
      (nativeLeg F).app p ≫ JTTargetCommaPullback.targetMap W x y Q := by
  let l := (decorated F).app p ≫ (underCocone W x y).app (displayed.obj p)
  let r := (nativeLeg F).app p ≫ JTTargetCommaPullback.targetMap W x y Q
  change l = r
  apply Under.UnderMorphism.ext
  apply ((IsPushout.of_hasPushout (u F) (ec F)).map
    ((CategoryTheory.evaluation (I (L := L)) SSet.{0}).obj p)).hom_ext
  · change (inc F).app p ≫ ((decorated F).app p).right ≫
        ((underCocone W x y).app (displayed.obj p)).right =
      (inc F).app p ≫ ((projection F).app p).right ≫
        (NecklaceCylinderAugmentation.augmentation (T F p) ((oldTime (time := time)).obj p) ≫
          ((original F).collapse.app p).map) ≫ Q.map
    rw [← Category.assoc ((inc F).app p), decorated_cylinder,
      ← Category.assoc ((inc F).app p), projection_cylinder]
    change (lift (horizontal F p) ((realizedParameter F).app p) ≫
        (cylinder (T F p)).app ((degree (L := L)).obj p)) ≫
          ((underCocone W x y).app (displayed.obj p)).right =
      ((π F).app p ≫ (cylinder (T F p)).app ((oldTime (time := time)).obj p)) ≫
        (NecklaceCylinderAugmentation.augmentation (T F p) ((oldTime (time := time)).obj p) ≫
          ((original F).collapse.app p).map) ≫ Q.map
    simp only [Category.assoc]
    rw [← Category.assoc ((cylinder (T F p)).app ((oldTime (time := time)).obj p))
      (NecklaceCylinderAugmentation.augmentation (T F p) ((oldTime (time := time)).obj p)),
      augmentation_cylinder]
    change lift (horizontal F p) ((realizedParameter F).app p) ≫
        (cylinder (T F p)).app ((degree (L := L)).obj p) ≫
          JTNecklaceEndpointCylinder.descend W x y (T F p) ((degree (L := L)).obj p)
            (OrderedLabelElements.label W b (displayed.obj p)) = _
    rw [descend_cylinder]
    exact (JTOrderedLabelPaddingPrismChainGraphs.raw F p).trans (Category.assoc _ _ _)
  · exact (Under.w l).trans (Under.w r).symm

/-- Evaluate every internal necklace of the covered reduced cylinder in the original fixed target. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced F) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTDecoratedIntervalCylinder.evaluateFromProjections Q displayed (reduced F) (decorated F)
    (nativeLeg F) (raw_square F)

private abbrev common := chainLabels W (b (W := W) (x := x) (y := y)) L
private abbrev old := oldLabels W (b (W := W) (x := x) (y := y)) L
private abbrev ord := ordinals W (b (W := W) (x := x) (y := y)) L
private abbrev α := chainToOriginal W (b (W := W) (x := x) (y := y)) L
private abbrev β := chainToRealized W (b (W := W) (x := x) (y := y)) L
private abbrev chainParameter := JTPrismChainGraphCover.parameter
  (JTOrderedLabelPaddingPrismChainGraphs.X F)
  (JTJointRelativeGraphFamily.originalParameter (original F))
  (toOriginal W (b (W := W) (x := x) (y := y)) L)

private abbrev commonDecorated : reduced F ⟶ common (L := L) ⋙ underDiagram W x y :=
  descendParameter F ord (chainParameter F)

private theorem graphParameter_comp (p : I (L := L)) {k l : SimplexCategory}
    (j : k ⟶ l) (θ : (graphCover F).obj p ⟶ J.obj k) :
    (lift (horizontal F p) θ ≫ (cylinder (T F p)).app k) ≫
      (JTNecklaceEndpointCylinder.value (T F p)).map j =
    lift (horizontal F p) (θ ≫ J.map j) ≫ (cylinder (T F p)).app l := by
  have h : lift (horizontal F p) θ ≫ (𝟙 (T F p).toSSet ⊗ₘ J.map j) =
      lift (horizontal F p) (θ ≫ J.map j) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
      exact (Category.comp_id _).trans (lift_fst _ _).symm
    · rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd]
      exact (lift_snd _ _).symm
  rw [Category.assoc, ← (cylinder (T F p)).naturality j]
  change lift (horizontal F p) θ ≫
    ((𝟙 (T F p).toSSet ⊗ₘ J.map j) ≫ (cylinder (T F p)).app l) = _
  rw [← Category.assoc, h]

private abbrev oldLift := JTParametrizedTargetFamilies.liftNatural (original F)
private abbrev DQ := JTTargetCommaPullback.diagram W x y Q

private theorem common_realized_square (p : I (L := L)) :
    (commonDecorated F).app p ≫ (underDiagram W x y).map (β.app p) =
      (decorated F).app p := by
  apply Under.UnderMorphism.ext
  apply ((IsPushout.of_hasPushout (u F) (ec F)).map
    ((CategoryTheory.evaluation (I (L := L)) SSet.{0}).obj p)).hom_ext
  · change (inc F).app p ≫ ((commonDecorated F).app p).right ≫
      ((underDiagram W x y).map (β.app p)).right =
        (inc F).app p ≫ ((decorated F).app p).right
    rw [← Category.assoc ((inc F).app p), parameter_cylinder, decorated_cylinder]
    let j := (toRealized W (b (W := W) (x := x) (y := y)) L).app p
    change (lift (horizontal F p) ((chainParameter F).app p) ≫
      (cylinder (T F p)).app (ord.obj p)) ≫
      (NecklaceCylinderJointDiagram.cylinderUnder.map
        ((OrderedLabelElements.projection W b).map (β.app p))).right =
      lift (horizontal F p) ((chainParameter F).app p ≫ J.map j) ≫
        (cylinder (T F p)).app (degree.obj p)
    rw [chainToRealized_projection]
    change _ ≫ (JTNecklaceEndpointCylinder.nativeMap (𝟙 (T F p)) (ord.obj p) ≫
      (JTNecklaceEndpointCylinder.value (T F p)).map j) = _
    rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp]
    exact graphParameter_comp F p j _
  · exact (Under.w ((commonDecorated F).app p ≫ (underDiagram W x y).map (β.app p))).trans
      (Under.w ((decorated F).app p)).symm

private theorem oldLift_decorated (p : I (L := L)) :
    (oldLift F).app p ≫ JTTargetCommaPullback.fst W x y Q (old.obj p) =
      JTParametrizedTargetLiftTransport.graph ((original F).parameter p) :=
  JTCylinderOverTarget.lift_decorated W x y Q (old.obj p) (T F p) (oldTime.obj p)
    (JTParametrizedTargetLiftTransport.graph ((original F).parameter p))
    ((original F).collapse.app p) ((original F).raw p)

private theorem oldLift_native (p : I (L := L)) :
    (oldLift F).app p ≫ JTTargetCommaPullback.snd W x y Q (old.obj p) =
      (JTDecoratedIntervalCylinder.native Q (D F) (oldTime (time := time))).app p := by
  rw [show (oldLift F).app p ≫ JTTargetCommaPullback.snd W x y Q (old.obj p) =
      JTCylinderOverTarget.native W x y Q (T F p) (oldTime.obj p)
        ((original F).collapse.app p) from
    JTCylinderOverTarget.lift_native W x y Q (old.obj p) (T F p) (oldTime.obj p)
      (JTParametrizedTargetLiftTransport.graph ((original F).parameter p))
      ((original F).collapse.app p) ((original F).raw p)]
  apply Under.UnderMorphism.ext
  rfl

private theorem common_original_square (p : I (L := L)) :
    (commonDecorated F).app p ≫ (underDiagram W x y).map (α.app p) =
      (projection F).app p ≫ JTParametrizedTargetLiftTransport.graph
        ((original F).parameter p) := by
  apply Under.UnderMorphism.ext
  apply ((IsPushout.of_hasPushout (u F) (ec F)).map
    ((CategoryTheory.evaluation (I (L := L)) SSet.{0}).obj p)).hom_ext
  · change (inc F).app p ≫ ((commonDecorated F).app p).right ≫
      ((underDiagram W x y).map (α.app p)).right =
        (inc F).app p ≫ ((projection F).app p).right ≫
          (JTParametrizedTargetLiftTransport.graph ((original F).parameter p)).right
    rw [← Category.assoc ((inc F).app p), parameter_cylinder,
      ← Category.assoc ((inc F).app p), projection_cylinder]
    let j := (toOriginal W (b (W := W) (x := x) (y := y)) L).app p
    let θ := (chainParameter F).app p
    let r := (π F).app p
    let k := OrderedLabelElements.degree W b (old.obj p)
    let n := (oldTime (time := time)).obj p
    let ψ := (original F).parameter p
    change (lift (horizontal F p) θ ≫ (cylinder (T F p)).app (ord.obj p)) ≫
      (NecklaceCylinderJointDiagram.cylinderUnder.map
        ((OrderedLabelElements.projection W b).map (α.app p))).right =
      (r ≫ (cylinder (T F p)).app n) ≫
        JTInterpolatedReducedCylinder.cylinderMap (T F p) ψ
    rw [chainToOriginal_projection]
    change _ ≫ (JTNecklaceEndpointCylinder.nativeMap (𝟙 (T F p)) (ord.obj p) ≫
      (JTNecklaceEndpointCylinder.value (T F p)).map j) = _
    rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp, graphParameter_comp,
      Category.assoc r, JTInterpolatedReducedCylinder.cylinderMap_cylinder]
    have hθ : θ ≫ J.map j = r ≫ ψ := NatTrans.congr_app
      (JTPrismChainGraphCover.parameter_projection
        (JTOrderedLabelPaddingPrismChainGraphs.X F)
        (JTJointRelativeGraphFamily.originalParameter (original F))
        (toOriginal W (b (W := W) (x := x) (y := y)) L)) p
    rw [hθ, ← Category.assoc r, comp_lift]
    rfl
  · exact (Under.w ((commonDecorated F).app p ≫ (underDiagram W x y).map (α.app p))).trans
      (Under.w ((projection F).app p ≫ JTParametrizedTargetLiftTransport.graph
        ((original F).parameter p))).symm

private theorem common_raw (p : I (L := L)) :
    (commonDecorated F).app p ≫ (underCocone W x y).app (common.obj p) =
      (nativeLeg F).app p ≫ JTTargetCommaPullback.targetMap W x y Q := by
  have h := (underCocone W x y).naturality (β.app p)
  have h' : (underDiagram W x y).map (β.app p) ≫
      (underCocone W x y).app (displayed.obj p) = (underCocone W x y).app (common.obj p) :=
    h.trans (Category.comp_id _)
  rw [← h', ← Category.assoc, common_realized_square F p]
  exact raw_square F p

private abbrev rightLift :=
  JTDecoratedIntervalCylinder.liftFromProjections Q displayed (reduced F) (decorated F)
    (nativeLeg F) (raw_square F)
private abbrev commonLift :=
  JTDecoratedIntervalCylinder.liftFromProjections Q common (reduced F) (commonDecorated F)
    (nativeLeg F) (common_raw F)

private theorem fixedTarget_square
    {i j : OrderedLabelElements.Index W (b (W := W) (x := x) (y := y))}
    {U V : Under B} (a : i ⟶ j) (r : U ⟶ V)
    (u₀ : U ⟶ DQ.obj i) (v₀ : V ⟶ DQ.obj j)
    {u₁ : U ⟶ (underDiagram W x y).obj i}
    {v₁ : V ⟶ (underDiagram W x y).obj j}
    {u₂ : U ⟶ BoundaryNecklaceComma.necklaceUnder.obj Q.code}
    {v₂ : V ⟶ BoundaryNecklaceComma.necklaceUnder.obj Q.code}
    (hu₁ : u₀ ≫ JTTargetCommaPullback.fst W x y Q i = u₁)
    (hv₁ : v₀ ≫ JTTargetCommaPullback.fst W x y Q j = v₁)
    (hu₂ : u₀ ≫ JTTargetCommaPullback.snd W x y Q i = u₂)
    (hv₂ : v₀ ≫ JTTargetCommaPullback.snd W x y Q j = v₂)
    (h₁ : u₁ ≫ (underDiagram W x y).map a = r ≫ v₁)
    (h₂ : u₂ = r ≫ v₂) :
    u₀ ≫ DQ.map a = r ≫ v₀ := by
  apply (IsPullback.of_hasPullback ((underCocone W x y).app j)
    (JTTargetCommaPullback.targetMap W x y Q)).hom_ext
  · change (u₀ ≫ DQ.map a) ≫ JTTargetCommaPullback.fst W x y Q j =
      (r ≫ v₀) ≫ JTTargetCommaPullback.fst W x y Q j
    rw [Category.assoc, JTTargetCommaPullback.map_fst W x y Q a,
      ← Category.assoc u₀, hu₁, Category.assoc r, hv₁]
    exact h₁
  · change (u₀ ≫ DQ.map a) ≫ JTTargetCommaPullback.snd W x y Q j =
      (r ≫ v₀) ≫ JTTargetCommaPullback.snd W x y Q j
    rw [Category.assoc, JTTargetCommaPullback.map_snd W x y Q a,
      hu₂, Category.assoc r, hv₂]
    exact h₂

private theorem commonLift_realized (p : I (L := L)) :
    (commonLift F).app p ≫ DQ.map (β.app p) = (rightLift F).app p := by
  have h₁ : (commonDecorated F).app p ≫ (underDiagram W x y).map (β.app p) =
      𝟙 _ ≫ (decorated F).app p :=
    (common_realized_square F p).trans (Category.id_comp _).symm
  have h₂ : (nativeLeg F).app p = 𝟙 _ ≫ (nativeLeg F).app p :=
    (Category.id_comp _).symm
  have h := fixedTarget_square (β.app p) (𝟙 _) ((commonLift F).app p) ((rightLift F).app p)
    (JTDecoratedIntervalCylinder.liftFromProjections_fst Q common _ _ _ _ p)
    (JTDecoratedIntervalCylinder.liftFromProjections_fst Q displayed _ _ _ _ p)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd Q common _ _ _ _ p)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd Q displayed _ _ _ _ p)
    h₁ h₂
  exact h.trans (Category.id_comp _)

private theorem commonLift_original (p : I (L := L)) :
    (commonLift F).app p ≫ DQ.map (α.app p) =
      (projection F).app p ≫ (oldLift F).app p :=
  fixedTarget_square (α.app p) ((projection F).app p) ((commonLift F).app p) ((oldLift F).app p)
    (JTDecoratedIntervalCylinder.liftFromProjections_fst Q common _ _ _ _ p)
    (oldLift_decorated F p)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd Q common _ _ _ _ p)
    (oldLift_native F p) (common_original_square F p) rfl

/-- The entire inverse-image boundary is retained in the presentation. -/
abbrev presentationProjection :
    BoundaryNecklaceComma.Presentation (reduced F) ⥤
      BoundaryNecklaceComma.Presentation (cylinders F (oldTime (time := time))) :=
  JTBoundaryNecklacePresentationCone.mapPresentation
    (cylinders F (oldTime (time := time))) (reduced F) (𝟭 (I (L := L)))
    (projection F)

private theorem cylinderHom_point_GW (T : NecklaceCode) (n : SimplexCategory) :
    DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.cylinderHom T n)) := by
  letI := NecklaceCylinderHomSpan.leftMap_weak T n
  letI : WeakEquivalence (C := SSet.{0})
      (DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.necklaceHom T)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DecoratedNecklaceHomBar.necklaceHom_point_GW T)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← DaggerOriginalProductGadget.pointIsTerminal.hom_ext
    (NecklaceCylinderHomSpan.leftMap T n ≫ DaggerOriginalProductGadget.pointMap _)
    (DaggerOriginalProductGadget.pointMap _)]
  infer_instance

/-- The full inverse-image chain presentation projects weakly to the old
parametrized cylinder, with no length or old-boundary mono condition. -/
theorem presentationProjection_weak :
    WeakEquivalence (nerveMap (presentationProjection F)) := by
  apply FullInverseImagePrism.diagram_presentationProjection_weak
    (π F) (d F) (e (time := time))
    (cylinders F (oldTime (time := time)))
    (cylinderLeg F (oldTime (time := time))) (old_boundary F)
  · intro p
    exact JTNecklaceEndpointCylinder.isPushout (T F p) ((oldTime (time := time)).obj p)
  · intro p
    exact JTOrderedLabelPaddingPrismChainGraphs.projection_trivialFibration F p
  · intro p
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (T F p) ((oldTime (time := time)).obj p)
  · exact JTParametrizedTargetFamilies.projection_weak

/-- The full covered presentation retains the weak type of the entire chain index. -/
theorem forget_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
      (reduced F)))) := by
  apply FullInverseImagePrism.diagram_forget_weak
    (π F) (d F) (e (time := time))
    (cylinders F (oldTime (time := time)))
    (cylinderLeg F (oldTime (time := time))) (old_boundary F)
  · intro p
    exact JTNecklaceEndpointCylinder.isPushout (T F p) ((oldTime (time := time)).obj p)
  · intro p
    exact JTOrderedLabelPaddingPrismChainGraphs.projection_trivialFibration F p
  · intro p
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (T F p) ((oldTime (time := time)).obj p)

/- The common reduced cylinder has the same two projections over both labels. -/
/-- Evaluation on the common restricted label, with the native map to the same fixed target. -/
def commonEvaluation : BoundaryNecklaceComma.Presentation (reduced F) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTDecoratedIntervalCylinder.evaluateFromProjections Q common (reduced F) (commonDecorated F)
    (nativeLeg F) (common_raw F)

/-- The common restricted evaluation maps naturally to the realized evaluation. -/
def compareRealized :=
  Functor.whiskerRight
    (JTBoundaryNecklacePresentationTransport.comparison DQ (reduced F)
      (commonLift F) (rightLift F) β (commonLift_realized F))
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

/-- The common restricted evaluation maps naturally to the evaluation on the original cylinders. -/
def compareOriginal :=
  Functor.whiskerRight
    (JTBoundaryNecklacePresentationTransport.comparisonReindexedWithSourceChange DQ
      (𝟭 (I (L := L))) (commonLift F) (oldLift F) (projection F) α
      (commonLift_original F))
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

section TailCone

open BoundaryNecklaceComma (fiberDiagram sourceCode necklaceUnder)

private abbrev chainBase :=
  base W (b (W := W) (x := x) (y := y)) L ⋙
    JTOrderedLabelPaddingPrismSliceArrow.originalBase W (b (W := W) (x := x) (y := y)) L

private abbrev originalCylinders :=
  JTParametrizedTargetFamilies.cylinders (L := L) (time := time)

private abbrev originalLift :=
  JTParametrizedTargetFamilies.liftNatural (Q := Q) (L := L) (time := time) F

private abbrev targetPresentation := JTTargetCommaPullback.toPullback W x y Q
private abbrev targetEvaluation := JTTargetCommaExactEvaluation.fromPresentation W x y Q

variable (tail : A ⥤ JTGraphFactoredPresentation.TargetComma Q)

private abbrev displayedTail := tail ⋙ targetPresentation (Q := Q)
private abbrev chainTail := chainBase (L := L) ⋙ displayedTail tail

variable (a : L ⟶ displayedTail tail ⋙ Grothendieck.forget (fiberDiagram (DQ (Q := Q))))
variable (n : originalCylinders (L := L) (time := time) ⟶
  displayedTail tail ⋙ sourceCode (DQ (Q := Q)) ⋙ necklaceUnder)

private abbrev chainLabelCollapse :
    common (L := L) ⟶ chainTail tail ⋙ Grothendieck.forget (fiberDiagram (DQ (Q := Q))) :=
  α ≫ Functor.whiskerLeft (chainBase (L := L)) a

private abbrev chainNativeCollapse :
    reduced F ⟶ chainTail tail ⋙ sourceCode (DQ (Q := Q)) ⋙ necklaceUnder :=
  projection F ≫ Functor.whiskerLeft (chainBase (L := L)) n

private theorem originalLift_app (i : I (L := L)) :
    (oldLift F).app i = (originalLift F).app ((chainBase (L := L)).obj i) := rfl

variable (hs : ∀ j, (originalLift F).app j ≫ (DQ (Q := Q)).map (a.app j) =
    n.app j ≫ ((displayedTail tail).obj j).fiber.hom)

include hs in
private theorem chainTail_square (i : I (L := L)) :
    (commonLift F).app i ≫ (DQ (Q := Q)).map ((chainLabelCollapse tail a).app i) =
      (chainNativeCollapse F tail n).app i ≫ ((chainTail tail).obj i).fiber.hom := by
  apply Under.UnderMorphism.ext
  let j := (chainBase (L := L)).obj i
  let p := ((commonLift F).app i).right
  let r := ((projection F).app i).right
  let q := ((oldLift F).app i).right
  let E := DQ (Q := Q)
  let g := ((displayedTail tail).obj j).fiber.hom.right
  let d := (E.map (a.app j)).right
  have h₁ : p ≫ (E.map (α.app i)).right = r ≫ q :=
    congrArg (fun f ↦ f.right) (commonLift_original F i)
  have hl : q = ((originalLift F).app j).right :=
    congrArg (fun f ↦ f.right) (originalLift_app F i)
  have h₂ : q ≫ d = (n.app j).right ≫ g :=
    (congrArg (· ≫ d) hl).trans (congrArg (fun f ↦ f.right) (hs j))
  have he : (E.map (α.app i ≫ a.app j)).right = (E.map (α.app i)).right ≫ d :=
    congrArg (fun f ↦ f.right) (E.map_comp (α.app i) (a.app j))
  change p ≫ (E.map (α.app i ≫ a.app j)).right = (r ≫ (n.app j).right) ≫ g
  rw [he, ← Category.assoc p, h₁, Category.assoc r, h₂, ← Category.assoc r]

private def evaluatePairedTail {K : Type} [SmallCategory K]
    (k : K ⥤ JTGraphFactoredPresentation.TargetComma Q) :
    (k ⋙ targetPresentation (Q := Q)) ⋙ targetEvaluation (Q := Q) ⟶ k := by
  let e := JTTargetCommaPullback.equivalence W x y Q
  let u : targetPresentation (Q := Q) ⋙ targetEvaluation (Q := Q) ⟶ 𝟭 _ :=
    Functor.whiskerLeft (targetPresentation (Q := Q))
      (JTTargetCommaExactEvaluation.inverseIso W x y Q).inv ≫ e.unitIso.inv
  exact eqToHom (Functor.assoc k (targetPresentation (Q := Q)) (targetEvaluation (Q := Q))) ≫
    Functor.whiskerLeft k u ≫ eqToHom (Functor.comp_id k)

/-- A compatible native and decorated cone on the original cylinders induces a comparison
on the covered cylinders, keeping their entire internal necklace diagrams. -/
def compareCommonToTail :
    commonEvaluation F ⟶
      Grothendieck.forget (fiberDiagram (reduced F)) ⋙ chainBase (L := L) ⋙ tail := by
  let g := Grothendieck.forget (fiberDiagram (reduced F))
  let k := g ⋙ chainBase (L := L) ⋙ tail
  let H := targetEvaluation (Q := Q)
  let σ := JTVariablePresentationCone.cone (DQ (Q := Q)) (reduced F) common (commonLift F)
    (chainTail tail) (chainLabelCollapse tail a) (chainNativeCollapse F tail n)
    (chainTail_square F tail a n hs)
  exact Functor.whiskerRight σ H ≫ evaluatePairedTail k

end TailCone

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismChainCylinder
