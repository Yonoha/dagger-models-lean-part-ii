import DaggerModelsPartII.JTActualJointChainCylinder
import DaggerModelsPartII.JTBoundaryNecklacePresentationTransport
import DaggerModelsPartII.FullInverseImagePrism

/-! Compare the full covered chain evaluation to the unchanged original family. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChainCylinderComparison

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTActualJointChoiceChainGraph (Index)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open JTNecklaceEndpointCylinder (cylinder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev old := JTActualJointChainLabels.oldLabels F j
private abbrev common := JTActualJointChainLabels.chainLabels F j
private abbrev α := JTActualJointChainLabels.chainToOriginal F j
private abbrev ord := JTActualJointChoiceChainGraph.ordinals F j
private abbrev oldTime :=
  JTActualJointChoiceChainGraph.base F j ⋙ JTActualJointChoiceCover.projection F j ⋙
    JTExactlyMarkedSourceDiagram.base F j ⋙ time
private abbrev original := JTActualJointChoiceChainGraph.original F j
private abbrev D := JTJointRelativeGraphFamily.native (original F j)
private abbrev T (p : Index F j) := ((D F j).obj p).left
private abbrev π := JTActualJointChoiceChainGraph.graphProjection F j
private abbrev θ := JTActualJointChainLabels.chainParameter F j
private abbrev reduced := JTActualJointChainCylinder.reduced F j
private abbrev ρ := JTActualJointChainCylinder.projection F j
private abbrev oldCylinders := JTDecoratedIntervalCylinder.reduced Q (D F j) (oldTime F j)
private abbrev DQ := JTTargetCommaPullback.diagram W x y Q
private abbrev chainNative := JTGraphCoveredLabelEvaluation.nativeLeg Q
  (common F j) (oldTime F j) (original F j).collapse (π F j)
private abbrev chainDecorated := JTGraphCoveredLabelEvaluation.decorated Q
  (common F j) (oldTime F j) (original F j).collapse (π F j) (θ F j)
private abbrev chainRaw := JTGraphCoveredLabelEvaluation.raw_square Q
  (common F j) (oldTime F j) (original F j).collapse (π F j) (θ F j)
  (JTActualJointChainLabels.raw F j)
private abbrev chainLift := JTDecoratedIntervalCylinder.liftFromProjections Q
  (common F j) (reduced F j) (chainDecorated F j) (chainNative F j) (chainRaw F j)
private abbrev oldLift := JTParametrizedTargetFamilies.liftNatural (original F j)

/-- The full inverse-image boundary survives in the source presentation. -/
abbrev presentationProjection :
    BoundaryNecklaceComma.Presentation (reduced F j) ⥤
      BoundaryNecklaceComma.Presentation (oldCylinders F j) :=
  JTBoundaryNecklacePresentationCone.mapPresentation
    (oldCylinders F j) (reduced F j) (𝟭 (Index F j)) (ρ F j)



private abbrev horizontal (p : Index F j) :=
  (π F j).app p ≫ fst (T F j p).toSSet (J.obj ((oldTime F j).obj p))

private theorem graphParameter_comp (p : Index F j) {k l : SimplexCategory}
    (g : k ⟶ l) (η : (JTActualJointChoiceChainGraph.graphCover F j).obj p ⟶ J.obj k) :
    (lift (horizontal F j p) η ≫ (cylinder (T F j p)).app k) ≫
      (JTNecklaceEndpointCylinder.value (T F j p)).map g =
    lift (horizontal F j p) (η ≫ J.map g) ≫ (cylinder (T F j p)).app l := by
  have h : lift (horizontal F j p) η ≫ (𝟙 (T F j p).toSSet ⊗ₘ J.map g) =
      lift (horizontal F j p) (η ≫ J.map g) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
      exact (Category.comp_id _).trans (lift_fst _ _).symm
    · rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd]
      exact (lift_snd _ _).symm
  rw [Category.assoc, ← (cylinder (T F j p)).naturality g]
  change lift (horizontal F j p) η ≫
    ((𝟙 (T F j p).toSSet ⊗ₘ J.map g) ≫ (cylinder (T F j p)).app l) = _
  rw [← Category.assoc, h]

private abbrev u := JTEndpointReducedPullbackCover.boundaryInclusion
  (π F j) (JTGraphCoveredLabelEvaluation.boundary Q (common F j) (oldTime F j)
    (original F j).collapse)
private abbrev ec := JTEndpointReducedPullbackCover.collapse
  (π F j) (JTGraphCoveredLabelEvaluation.boundary Q (common F j) (oldTime F j)
    (original F j).collapse)
  (Functor.whiskerLeft (oldTime F j) JTXiEndpointCollapse.cylinderProjection)
private abbrev inc := pushout.inl (u F j) (ec F j)

private theorem chainDecorated_cylinder (p : Index F j) :
    (inc F j).app p ≫ ((chainDecorated F j).app p).right =
      lift (horizontal F j p) ((θ F j).app p) ≫
        (cylinder (T F j p)).app ((ord F j).obj p) := by
  exact JTEndpointReducedCover.descend_cylinder _ _ _ _ _ p

private theorem projection_cylinder (p : Index F j) :
    (inc F j).app p ≫ ((ρ F j).app p).right =
      (π F j).app p ≫ (cylinder (T F j p)).app ((oldTime F j).obj p) := by
  exact JTEndpointReducedPullbackCover.projection_cylinder _ _ _ _ _ _ p

private theorem chainDecorated_original (p : Index F j) :
    (chainDecorated F j).app p ≫ (underDiagram W x y).map ((α F j).app p) =
      (ρ F j).app p ≫ JTParametrizedTargetLiftTransport.graph
        ((original F j).parameter p) := by
  apply Under.UnderMorphism.ext
  apply ((IsPushout.of_hasPushout (u F j) (ec F j)).map
    ((CategoryTheory.evaluation (Index F j) SSet.{0}).obj p)).hom_ext
  · change (inc F j).app p ≫ ((chainDecorated F j).app p).right ≫
        ((underDiagram W x y).map ((α F j).app p)).right =
      (inc F j).app p ≫ ((ρ F j).app p).right ≫
        (JTParametrizedTargetLiftTransport.graph ((original F j).parameter p)).right
    rw [← Category.assoc ((inc F j).app p), chainDecorated_cylinder,
      ← Category.assoc ((inc F j).app p), projection_cylinder]
    let g := (JTActualJointChoiceChainGraph.toOriginal F j).app p
    let η := (θ F j).app p
    let r := (π F j).app p
    let k := OrderedLabelElements.degree W (boundaryPoint W x y) ((old F j).obj p)
    let n := (oldTime F j).obj p
    let ψ := (original F j).parameter p
    change (lift (horizontal F j p) η ≫ (cylinder (T F j p)).app ((ord F j).obj p)) ≫
      (NecklaceCylinderJointDiagram.cylinderUnder.map
        ((OrderedLabelElements.projection W (boundaryPoint W x y)).map
          ((α F j).app p))).right =
      (r ≫ (cylinder (T F j p)).app n) ≫
        JTInterpolatedReducedCylinder.cylinderMap (T F j p) ψ
    rw [JTActualJointChainLabels.chainToOriginal_projection]
    change _ ≫ (JTNecklaceEndpointCylinder.nativeMap (𝟙 (T F j p))
      ((ord F j).obj p) ≫ (JTNecklaceEndpointCylinder.value (T F j p)).map g) = _
    rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp,
      graphParameter_comp, Category.assoc r,
      JTInterpolatedReducedCylinder.cylinderMap_cylinder]
    have hθ : η ≫ J.map g = r ≫ ψ :=
      NatTrans.congr_app (JTActualJointChoiceChainGraph.graphParameter_projection F j) p
    rw [hθ, ← Category.assoc r, comp_lift]
    rfl
  · exact (Under.w ((chainDecorated F j).app p ≫
      (underDiagram W x y).map ((α F j).app p))).trans
        (Under.w ((ρ F j).app p ≫
          JTParametrizedTargetLiftTransport.graph ((original F j).parameter p))).symm



private theorem oldLift_decorated (p : Index F j) :
    (oldLift F j).app p ≫ JTTargetCommaPullback.fst W x y Q ((old F j).obj p) =
      JTParametrizedTargetLiftTransport.graph ((original F j).parameter p) :=
  JTCylinderOverTarget.lift_decorated W x y Q ((old F j).obj p)
    (T F j p) ((oldTime F j).obj p)
    (JTParametrizedTargetLiftTransport.graph ((original F j).parameter p))
    ((original F j).collapse.app p) ((original F j).raw p)

private theorem oldLift_native (p : Index F j) :
    (oldLift F j).app p ≫ JTTargetCommaPullback.snd W x y Q ((old F j).obj p) =
      (JTDecoratedIntervalCylinder.native Q (D F j) (oldTime F j)).app p := by
  rw [show (oldLift F j).app p ≫ JTTargetCommaPullback.snd W x y Q ((old F j).obj p) =
      JTCylinderOverTarget.native W x y Q (T F j p) ((oldTime F j).obj p)
        ((original F j).collapse.app p) from
    JTCylinderOverTarget.lift_native W x y Q ((old F j).obj p)
      (T F j p) ((oldTime F j).obj p)
      (JTParametrizedTargetLiftTransport.graph ((original F j).parameter p))
      ((original F j).collapse.app p) ((original F j).raw p)]
  apply Under.UnderMorphism.ext
  rfl

private theorem fixedTarget_square
    {a b : OrderedLabelElements.Index W (boundaryPoint W x y)}
    {U V : Under B} (f : a ⟶ b) (r : U ⟶ V)
    (u₀ : U ⟶ (DQ (Q := Q)).obj a) (v₀ : V ⟶ (DQ (Q := Q)).obj b)
    {u₁ : U ⟶ (underDiagram W x y).obj a}
    {v₁ : V ⟶ (underDiagram W x y).obj b}
    {u₂ : U ⟶ BoundaryNecklaceComma.necklaceUnder.obj Q.code}
    {v₂ : V ⟶ BoundaryNecklaceComma.necklaceUnder.obj Q.code}
    (hu₁ : u₀ ≫ JTTargetCommaPullback.fst W x y Q a = u₁)
    (hv₁ : v₀ ≫ JTTargetCommaPullback.fst W x y Q b = v₁)
    (hu₂ : u₀ ≫ JTTargetCommaPullback.snd W x y Q a = u₂)
    (hv₂ : v₀ ≫ JTTargetCommaPullback.snd W x y Q b = v₂)
    (h₁ : u₁ ≫ (underDiagram W x y).map f = r ≫ v₁)
    (h₂ : u₂ = r ≫ v₂) :
    u₀ ≫ (DQ (Q := Q)).map f = r ≫ v₀ := by
  apply (IsPullback.of_hasPullback ((underCocone W x y).app b)
    (JTTargetCommaPullback.targetMap W x y Q)).hom_ext
  · change (u₀ ≫ (DQ (Q := Q)).map f) ≫ JTTargetCommaPullback.fst W x y Q b =
      (r ≫ v₀) ≫ JTTargetCommaPullback.fst W x y Q b
    rw [Category.assoc, JTTargetCommaPullback.map_fst W x y Q f,
      ← Category.assoc u₀, hu₁, Category.assoc r, hv₁]
    exact h₁
  · change (u₀ ≫ (DQ (Q := Q)).map f) ≫ JTTargetCommaPullback.snd W x y Q b =
      (r ≫ v₀) ≫ JTTargetCommaPullback.snd W x y Q b
    rw [Category.assoc, JTTargetCommaPullback.map_snd W x y Q f,
      hu₂, Category.assoc r, hv₂]
    exact h₂

private theorem chainLift_original (p : Index F j) :
    (chainLift F j).app p ≫ (DQ (Q := Q)).map ((α F j).app p) =
      (ρ F j).app p ≫ (oldLift F j).app p :=
  fixedTarget_square ((α F j).app p) ((ρ F j).app p)
    ((chainLift F j).app p) ((oldLift F j).app p)
    (JTDecoratedIntervalCylinder.liftFromProjections_fst Q (common F j) _ _ _ _ p)
    (oldLift_decorated F j p)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd Q (common F j) _ _ _ _ p)
    (oldLift_native F j p) (chainDecorated_original F j p) rfl

/-- Natural comparison of every internal-necklace evaluation to the unchanged
original family evaluation in the fixed target comma. -/
def compareOriginal :=
  Functor.whiskerRight
    (JTBoundaryNecklacePresentationTransport.comparisonReindexedWithSourceChange
      (DQ (Q := Q)) (𝟭 (Index F j)) (chainLift F j) (oldLift F j)
      (ρ F j) (α F j) (chainLift_original F j))
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)



private def cylinderLeg :
    JTActualJointChoiceChainGraph.X F j ⟶
      oldCylinders F j ⋙ Under.forget B where
  app p := (cylinder (T F j p)).app ((oldTime F j).obj p)
  naturality _ _ f :=
    (JTDecoratedIntervalCylinder.reduced_map_cylinder Q (D F j) (oldTime F j) f).symm

private theorem old_boundary :
    JTGraphCoveredLabelEvaluation.boundary Q (common F j) (oldTime F j)
        (original F j).collapse ≫ cylinderLeg F j =
      Functor.whiskerLeft (oldTime F j) JTXiEndpointCollapse.cylinderProjection ≫
        JTEndpointReducedCover.boundary (oldCylinders F j) := by
  apply NatTrans.ext
  funext p
  exact (JTNecklaceEndpointCylinder.isPushout (T F j p) ((oldTime F j).obj p)).w

private theorem cylinderHom_point_GW (S : NecklaceCode) (n : SimplexCategory) :
    DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.cylinderHom S n)) := by
  letI := NecklaceCylinderHomSpan.leftMap_weak S n
  letI : WeakEquivalence (C := SSet.{0})
      (DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.necklaceHom S)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DecoratedNecklaceHomBar.necklaceHom_point_GW S)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← DaggerOriginalProductGadget.pointIsTerminal.hom_ext
    (NecklaceCylinderHomSpan.leftMap S n ≫ DaggerOriginalProductGadget.pointMap _)
    (DaggerOriginalProductGadget.pointMap _)]
  infer_instance

/-- The entire covered presentation projects weakly to the unchanged original
cylinder presentation; this does not require positive target length. -/
theorem presentationProjection_weak :
    WeakEquivalence (nerveMap (presentationProjection F j)) := by
  apply FullInverseImagePrism.diagram_presentationProjection_weak
    (π F j)
    (JTGraphCoveredLabelEvaluation.boundary Q (common F j) (oldTime F j)
      (original F j).collapse)
    (Functor.whiskerLeft (oldTime F j) JTXiEndpointCollapse.cylinderProjection)
    (oldCylinders F j) (cylinderLeg F j) (old_boundary F j)
  · intro p
    exact JTNecklaceEndpointCylinder.isPushout (T F j p) ((oldTime F j).obj p)
  · intro p
    exact JTActualJointChoiceChainGraph.graphProjection_trivialFibration F j p
  · intro p
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (T F j p) ((oldTime F j).obj p)
  · exact JTParametrizedTargetFamilies.projection_weak


end
end DaggerModels.PartII.JTActualJointChainCylinderComparison
