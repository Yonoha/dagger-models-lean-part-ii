import DaggerModelsPartII.JTDecoratedIntervalCylinder
import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange
import DaggerModelsPartII.JTJointRelativeGraphFamily
import DaggerModelsPartII.JTNecklaceCylinderConnector
import DaggerModelsPartII.FullInverseImagePrism
import DaggerModelsPartII.NecklaceCylinderHomSpan

/-!
# Evaluation of a covered graph after complete endpoint collapse

A natural parameter on a source cover descends along both complete inverse-image
endpoint lines. The raw image equation gives the two exact fixed-target legs.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open EnrichedCategory DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFullBoundaryGraphEvaluation

open JTJointRelativeGraphFamily (native coefficient RawOn productBoundary)
open JTJointRelativeParameters (withTime)
open JTParametrizedTargetFamilies (Family codes)
open JTTargetIntervalOverMapping (whole)
open JTNecklaceEndpointCylinder (cylinder)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open DaggerOriginalProductGadget (pointMap pointIsTerminal)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time)

private abbrev code (p : I) := (codes L).obj p

private abbrev product (v : I ⥤ SimplexCategory) :=
  withTime Q.map J v (native F) (whole Q.code)

private abbrev cylinders (v : I ⥤ SimplexCategory) :=
  JTDecoratedIntervalCylinder.reduced Q (native F) v

variable {X : I ⥤ SSet.{0}} (π : X ⟶ product F time)

private abbrev e :=
  Functor.whiskerLeft time JTXiEndpointCollapse.cylinderProjection

private abbrev u := JTEndpointReducedPullbackCover.u π (productBoundary F)
private abbrev v := JTEndpointReducedPullbackCover.v π (productBoundary F)
private abbrev ec := JTEndpointReducedPullbackCover.collapse π (productBoundary F) (e (time := time))

private def cylinderLeg (v : I ⥤ SimplexCategory) :
    product F v ⟶ cylinders F v ⋙ Under.forget B where
  app p := (cylinder (code (L := L) p)).app (v.obj p)
  naturality _ _ f :=
    (JTDecoratedIntervalCylinder.reduced_map_cylinder Q (native F) v f).symm

private theorem old_boundary :
    productBoundary F ≫ cylinderLeg F time =
      e (time := time) ≫ JTEndpointReducedCover.boundary (cylinders F time) := by
  apply NatTrans.ext
  funext p
  exact (JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p)).w

/-- Reduce the covered product along the full inverse image of both endpoint lines. -/
abbrev reduced :=
  JTEndpointReducedPullbackCover.reduced π (productBoundary F) (e (time := time))

/-- The full inverse-image reduction maps to the original time cylinder under its endpoints. -/
def projection : reduced F π ⟶ cylinders F time :=
  JTEndpointReducedPullbackCover.projection π (productBoundary F) (e (time := time))
    (cylinders F time) (cylinderLeg F time) (old_boundary F)

variable (θ : X ⟶ coefficient (L := L) ⋙ J)

private def graphProduct : X ⟶ product F (coefficient (L := L)) where
  app p := lift (π.app p ≫ fst (code (L := L) p).toSSet (J.obj (time.obj p))) (θ.app p)
  naturality {p q} f := by
    change _ = _ ≫ ((JTDecoratedIntervalDiagram.parameterize Q.map J (coefficient (L := L))
      (native F ⋙ whole Q.code)).map f).left
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      let a := X.map f
      let g := ((native F).map f).left.map
      let n := time.map f
      have hfst : (product F time).map f ≫
          fst (code (L := L) q).toSSet (J.obj (time.obj q)) =
        fst (code (L := L) p).toSSet (J.obj (time.obj p)) ≫ g := by
        change ((JTDecoratedIntervalDiagram.parameterize Q.map J time
          (native F ⋙ whole Q.code)).map f).left ≫ _ = _
        rw [JTDecoratedIntervalDiagram.parameterize_map_left]
        exact tensorHom_fst g (J.map n)
      let v₁ := fst (code (L := L) q).toSSet (J.obj (time.obj q))
      let v₀ := fst (code (L := L) p).toSSet (J.obj (time.obj p))
      change a ≫ π.app q ≫ v₁ = (π.app p ≫ v₀) ≫ g
      calc
        _ = π.app p ≫ (product F time).map f ≫ v₁ := by
          rw [← Category.assoc a, π.naturality f, Category.assoc]
        _ = π.app p ≫ v₀ ≫ g := congrArg (π.app p ≫ ·) hfst
        _ = _ := (Category.assoc _ _ _).symm
    · simp only [Category.assoc, lift_snd]
      change X.map f ≫ θ.app q = θ.app p ≫ J.map ((coefficient (L := L)).map f)
      exact θ.naturality f

private abbrev graphLeg : X ⟶ L ⋙ underDiagram W x y ⋙ Under.forget B :=
  graphProduct F π θ ≫ cylinderLeg F (coefficient (L := L))

private theorem graph_boundary :
    u F π ≫ graphLeg F π θ = ec F π ≫ JTEndpointReducedCover.boundary (L ⋙ underDiagram W x y) := by
  apply NatTrans.ext
  funext p
  let i := (u F π).app p
  let r := (v F π).app p
  let k := (coefficient (L := L)).obj p
  let T := code (L := L) p
  let d := (productBoundary F).app p
  have h := NatTrans.congr_app (JTEndpointReducedPullbackCover.boundary_square π
    (productBoundary F)) p
  change i ≫ π.app p = r ≫ d at h
  change i ≫ lift (π.app p ≫ fst T.toSSet (J.obj (time.obj p))) (θ.app p) ≫
      (cylinder T).app k =
    (r ≫ (e (time := time)).app p) ≫ (JTNecklaceEndpointCylinder.boundary T).app k
  rw [← Category.assoc, comp_lift, ← Category.assoc i, h, Category.assoc r]
  change lift (r ≫ (JTNecklaceEndpointCylinder.endpointInclusion T ⊗ₘ 𝟙 _) ≫ fst _ _)
      (i ≫ θ.app p) ≫ (cylinder T).app k = _
  rw [tensorHom_fst, ← Category.assoc r]
  exact JTNecklaceCylinderConnector.boundary_collapse T k
    (r ≫ (e (time := time)).app p) (i ≫ θ.app p)

/-- The covered graph parameter gives a map to the original decorated cylinder. -/
def decorated : reduced F π ⟶ L ⋙ underDiagram W x y :=
  JTEndpointReducedCover.descend (u F π) (ec F π) (L ⋙ underDiagram W x y)
    (graphLeg F π θ) (graph_boundary F π θ)

/-- The native leg uses the same fixed target necklace as the original family. -/
def nativeProjection :
    reduced F π ⟶ (Functor.const I).obj (BoundaryNecklaceComma.necklaceUnder.obj Q.code) :=
  projection F π ≫ JTDecoratedIntervalCylinder.native Q (native F) time

private abbrev coveredCylinderLeg := pushout.inl (u F π) (ec F π)

private theorem projection_cylinder (p : I) :
    (coveredCylinderLeg F π).app p ≫ ((projection F π).app p).right =
      π.app p ≫ (cylinderLeg F time).app p :=
  JTEndpointReducedPullbackCover.projection_cylinder π (productBoundary F) (e (time := time))
    (cylinders F time) (cylinderLeg F time) (old_boundary F) p

private theorem decorated_cylinder (p : I) :
    (coveredCylinderLeg F π).app p ≫ ((decorated F π θ).app p).right =
      (graphLeg F π θ).app p :=
  JTEndpointReducedCover.descend_cylinder (u F π) (ec F π)
    (L ⋙ underDiagram W x y) (graphLeg F π θ) (graph_boundary F π θ) p

private theorem covered_isPushout (p : I) :
    IsPushout ((u F π).app p) ((ec F π).app p) ((coveredCylinderLeg F π).app p)
      ((reduced F π).obj p).hom :=
  (IsPushout.of_hasPushout (u F π) (ec F π)).map ((evaluation I SSet.{0}).obj p)

variable (hRaw : RawOn F π θ)

include hRaw in
/-- The decorated map and native collapse commute over the original raw target. -/
theorem pair_square (p : I) :
    (decorated F π θ).app p ≫ (underCocone W x y).app (L.obj p) =
      (nativeProjection F π).app p ≫ JTTargetCommaPullback.targetMap W x y Q := by
  let g := (decorated F π θ).app p ≫ (underCocone W x y).app (L.obj p)
  let h := (nativeProjection F π).app p ≫ JTTargetCommaPullback.targetMap W x y Q
  change g = h
  apply Under.UnderMorphism.ext
  apply (covered_isPushout F π p).hom_ext
  · let i := (coveredCylinderLeg F π).app p
    change i ≫ (((decorated F π θ).app p).right ≫
      ((underCocone W x y).app (L.obj p)).right) =
        i ≫ (((projection F π).app p).right ≫
          ((JTDecoratedIntervalCylinder.native Q (native F) time).app p).right) ≫ Q.map
    rw [← Category.assoc i, decorated_cylinder, ← Category.assoc i,
      ← Category.assoc i, projection_cylinder]
    let T := code (L := L) p
    let n := time.obj p
    let k := (coefficient (L := L)).obj p
    change (((graphProduct F π θ).app p ≫ (cylinder T).app k) ≫
        ((underCocone W x y).app (L.obj p)).right) =
      ((π.app p ≫ (cylinder T).app n) ≫
        (NecklaceCylinderAugmentation.augmentation T n ≫ (F.collapse.app p).map)) ≫ Q.map
    simp only [Category.assoc]
    rw [← Category.assoc ((cylinder T).app n) (NecklaceCylinderAugmentation.augmentation T n),
      NecklaceCylinderAugmentation.augmentation_cylinder]
    exact hRaw p
  · exact (Under.w g).trans (Under.w h).symm

/-- Evaluate all internal necklaces in the original fixed-target comma category. -/
def evaluate :
    BoundaryNecklaceComma.Presentation (reduced F π) ⥤ JTGraphFactoredPresentation.TargetComma Q :=
  JTDecoratedIntervalCylinder.evaluateFromProjections Q L _ (decorated F π θ)
    (nativeProjection F π) (pair_square F π θ hRaw)

private theorem cylinderHom_point_GW (T : NecklaceCode) (n : SimplexCategory) :
    GW (pointMap (NecklaceCylinderHomSpan.cylinderHom T n)) := by
  letI := NecklaceCylinderHomSpan.leftMap_weak T n
  letI : WeakEquivalence (C := SSet.{0}) (pointMap (NecklaceCylinderHomSpan.necklaceHom T)) :=
    (weakEquivalence_iff_GW _).mpr (DecoratedNecklaceHomBar.necklaceHom_point_GW T)
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (NecklaceCylinderHomSpan.leftMap T n ≫ pointMap _) (pointMap _)]
  infer_instance

/-- A levelwise trivial fibration suffices for the covered presentation to
retain the weak type of the entire indexing category. -/
theorem forget_weak (hπ : ∀ p, trivialFibrations SSet.{0} (π.app p)) :
    WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F π)))) := by
  apply FullInverseImagePrism.diagram_forget_weak π (productBoundary F) (e (time := time))
    (cylinders F time) (cylinderLeg F time) (old_boundary F)
  · intro p
    exact JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p)
  · exact hπ
  · intro p
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (code (L := L) p) (time.obj p)

/-- The projection retains every original internal necklace and every original arrow. -/
abbrev presentationProjection :
    BoundaryNecklaceComma.Presentation (reduced F π) ⥤
      BoundaryNecklaceComma.Presentation (cylinders F time) :=
  JTBoundaryNecklacePresentationCone.mapPresentation (cylinders F time)
    (reduced F π) (𝟭 I) (projection F π)

/-- For levelwise trivial fibrations this comparison of full presentations is weak. -/
theorem presentationProjection_weak (hπ : ∀ p, trivialFibrations SSet.{0} (π.app p)) :
    WeakEquivalence (nerveMap (presentationProjection F π)) := by
  apply FullInverseImagePrism.diagram_presentationProjection_weak π (productBoundary F)
    (e (time := time)) (cylinders F time) (cylinderLeg F time) (old_boundary F)
  · intro p
    exact JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p)
  · exact hπ
  · intro p
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (code (L := L) p) (time.obj p)
  · exact JTParametrizedTargetFamilies.projection_weak

private def compareProjection {K A : Type} [SmallCategory K] [SmallCategory A]
    {Y₀ Y₁ : K ⥤ Under B} {labels : K ⥤ A}
    (E : A ⥤ Under B) (p₀ : Y₀ ⟶ labels ⋙ E) (p₁ : Y₁ ⟶ labels ⋙ E)
    (r : Y₀ ⟶ Y₁) (h : ∀ p, p₀.app p = r.app p ≫ p₁.app p)
    {C : Type} [SmallCategory C]
    (H : BoundaryNecklaceComma.Presentation E ⥤ C) :
    (JTBoundaryNecklacePresentationCone.mapPresentation E Y₀ labels p₀) ⋙ H ⟶
      JTBoundaryNecklacePresentationCone.mapPresentation Y₁ Y₀ (𝟭 K) r ⋙
        (JTBoundaryNecklacePresentationCone.mapPresentation E Y₁ labels p₁ ⋙ H) := by
  let α : (𝟭 K) ⋙ labels ⟶ labels :=
    { app := fun p ↦ 𝟙 (labels.obj p)
      naturality := by intros; simp }
  let τ := JTBoundaryNecklacePresentationTransport.comparisonReindexedWithSourceChange
    E (𝟭 K) p₀ p₁ r α (fun p ↦ by
      change p₀.app p ≫ E.map (𝟙 (labels.obj p)) = r.app p ≫ p₁.app p
      exact (congrArg (p₀.app p ≫ ·) (E.map_id (labels.obj p))).trans
        ((Category.comp_id (p₀.app p)).trans (h p)))
  exact Functor.whiskerRight τ H

section OriginalComparison

private abbrev originalGraph (p : I) :=
  JTParametrizedTargetLiftTransport.graph (i := L.obj p) (F.parameter p)

private abbrev DQ := JTTargetCommaPullback.diagram W x y Q
private abbrev oldLift := JTParametrizedTargetFamilies.liftNatural F

variable (hGraph : ∀ p, (graphLeg F π θ).app p =
  π.app p ≫ (cylinderLeg F time).app p ≫ (originalGraph F p).right)

include hGraph in
private theorem decorated_original (p : I) :
    (decorated F π θ).app p = (projection F π).app p ≫ originalGraph F p := by
  apply Under.UnderMorphism.ext
  apply (covered_isPushout F π p).hom_ext
  · change (coveredCylinderLeg F π).app p ≫ ((decorated F π θ).app p).right =
      (coveredCylinderLeg F π).app p ≫ ((projection F π).app p).right ≫
        (originalGraph F p).right
    rw [decorated_cylinder, ← Category.assoc, projection_cylinder, Category.assoc]
    exact hGraph p
  · exact (Under.w ((decorated F π θ).app p)).trans
      (Under.w ((projection F π).app p ≫ originalGraph F p)).symm

private abbrev newLift :=
  JTDecoratedIntervalCylinder.liftFromProjections Q L (reduced F π) (decorated F π θ)
    (nativeProjection F π) (pair_square F π θ hRaw)

private theorem oldLift_fst (p : I) :
    (oldLift F).app p ≫ JTTargetCommaPullback.fst W x y Q (L.obj p) = originalGraph F p :=
  JTCylinderOverTarget.lift_decorated W x y Q (L.obj p) (code (L := L) p) (time.obj p)
    (originalGraph F p) (F.collapse.app p) (F.raw p)

private theorem oldLift_snd (p : I) :
    (oldLift F).app p ≫ JTTargetCommaPullback.snd W x y Q (L.obj p) =
      (JTDecoratedIntervalCylinder.native Q (native F) time).app p := by
  rw [show (oldLift F).app p ≫ JTTargetCommaPullback.snd W x y Q (L.obj p) =
      JTCylinderOverTarget.native W x y Q (code (L := L) p) (time.obj p)
        (F.collapse.app p) from
    JTCylinderOverTarget.lift_native W x y Q (L.obj p) (code (L := L) p) (time.obj p)
      (originalGraph F p) (F.collapse.app p) (F.raw p)]
  apply Under.UnderMorphism.ext
  rfl

include hGraph in
private theorem lift_original (p : I) :
    (newLift F π θ hRaw).app p = (projection F π).app p ≫ (oldLift F).app p := by
  apply (IsPullback.of_hasPullback ((underCocone W x y).app (L.obj p))
    (JTTargetCommaPullback.targetMap W x y Q)).hom_ext
  · change (newLift F π θ hRaw).app p ≫ JTTargetCommaPullback.fst W x y Q (L.obj p) =
      ((projection F π).app p ≫ (oldLift F).app p) ≫
        JTTargetCommaPullback.fst W x y Q (L.obj p)
    rw [JTDecoratedIntervalCylinder.liftFromProjections_fst, Category.assoc, oldLift_fst]
    exact decorated_original F π θ hGraph p
  · change (newLift F π θ hRaw).app p ≫ JTTargetCommaPullback.snd W x y Q (L.obj p) =
      ((projection F π).app p ≫ (oldLift F).app p) ≫
        JTTargetCommaPullback.snd W x y Q (L.obj p)
    rw [JTDecoratedIntervalCylinder.liftFromProjections_snd, Category.assoc, oldLift_snd]
    rfl

set_option maxHeartbeats 450000 in
/-- Exact graph agreement gives a natural comparison to the original evaluation
after projecting every internal necklace. -/
def compareOriginal :
    evaluate F π θ hRaw ⟶ presentationProjection F π ⋙ JTParametrizedTargetFamilies.evaluate F :=
  compareProjection (DQ (Q := Q)) (newLift F π θ hRaw) (oldLift F) (projection F π)
    (lift_original F π θ hRaw hGraph) (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

end OriginalComparison

end

end DaggerModels.PartII.JTFullBoundaryGraphEvaluation
