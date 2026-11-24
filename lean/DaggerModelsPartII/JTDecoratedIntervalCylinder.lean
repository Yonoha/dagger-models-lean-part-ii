import DaggerModelsPartII.JTDecoratedIntervalDiagram
import DaggerModelsPartII.JTCylinderOverTarget
import DaggerModelsPartII.JTPointwisePullbackLift
import DaggerModelsPartII.JTTargetCommaExactEvaluation
import DaggerModelsPartII.JTBoundaryNecklacePresentationCone

/-! Passage from coherent raw decorated lifts to the actual reduced cylinders. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalCylinder

open JTNecklaceEndpointCylinder (endpointInclusion value boundary cylinder nativeMap
  nativeMap_cylinder isPushout)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open JTDecoratedIntervalDiagram (wholeRaw parameterize_map_left)
open JTTargetIntervalOverMapping (whole)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

variable {I : Type} [SmallCategory I]
variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (D : I ⥤ Over Q.code) (time : I ⥤ SimplexCategory)

private abbrev code (i : I) := (D.obj i).left
private abbrev joint := (D ⋙ Over.forget Q.code).prod' time

/-- The original reduced source cylinders, with both varying operators. -/
abbrev reduced := joint Q D time ⋙ NecklaceCylinderJointDiagram.cylinderUnder

variable (labels : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (a : wholeRaw J time Q D ⟶ labels ⋙ JTDecoratedCylinderOverMapping.rawTarget W x y)

/-- Endpoint condition for a family of raw product maps. -/
def BoundaryEquation : Prop :=
  ∀ p, (endpointInclusion (code Q D p) ⊗ₘ 𝟙 (J.obj (time.obj p))) ≫ (a.app p).left =
    fst B (J.obj (time.obj p)) ≫ ((underDiagram W x y).obj (labels.obj p)).hom

variable (ha : BoundaryEquation Q D time labels a)

private def descendApp (p : I) :
    (reduced Q D time).obj p ⟶ (underDiagram W x y).obj (labels.obj p) :=
  let sq := isPushout (code Q D p) (time.obj p)
  Under.homMk (sq.desc (a.app p).left
    ((underDiagram W x y).obj (labels.obj p)).hom (ha p)) (sq.inr_desc _ _ _)

private theorem descendApp_cylinder (p : I) :
    (cylinder (code Q D p)).app (time.obj p) ≫ (descendApp Q D time labels a ha p).right =
      (a.app p).left :=
  (isPushout (code Q D p) (time.obj p)).inl_desc _ _ _

theorem reduced_map_cylinder {p p' : I} (f : p ⟶ p') :
    (cylinder (code Q D p)).app (time.obj p) ≫ ((reduced Q D time).map f).right =
      ((wholeRaw J time Q D).map f).left ≫ (cylinder (code Q D p')).app (time.obj p') := by
  rw [parameterize_map_left]
  let F := (D.map f).left
  let g := time.map f
  change (cylinder (code Q D p)).app (time.obj p) ≫
      (nativeMap F (time.obj p) ≫ (value (code Q D p')).map g) =
    (F.map ⊗ₘ J.map g) ≫ (cylinder (code Q D p')).app (time.obj p')
  rw [← Category.assoc, nativeMap_cylinder, Category.assoc]
  rw [← (cylinder (code Q D p')).naturality g, ← Category.assoc]
  change ((F.map ⊗ₘ 𝟙 (J.obj (time.obj p))) ≫
    (𝟙 (code Q D p').toSSet ⊗ₘ J.map g)) ≫ (cylinder (code Q D p')).app (time.obj p') = _
  rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/-- Descent uses the actual reduced-cylinder pushout and is natural in the
whole native, time, and decorated diagram. -/
def descend : reduced Q D time ⟶ labels ⋙ underDiagram W x y where
  app := descendApp Q D time labels a ha
  naturality p p' f := by
    let u := (reduced Q D time).map f ≫ descendApp Q D time labels a ha p'
    let v := descendApp Q D time labels a ha p ≫ (labels ⋙ underDiagram W x y).map f
    change u = v
    apply Under.UnderMorphism.ext
    apply (isPushout (code Q D p) (time.obj p)).hom_ext
    · change (cylinder (code Q D p)).app (time.obj p) ≫
        (((reduced Q D time).map f).right ≫ (descendApp Q D time labels a ha p').right) =
        (cylinder (code Q D p)).app (time.obj p) ≫
          ((descendApp Q D time labels a ha p).right ≫
            ((underDiagram W x y).map (labels.map f)).right)
      rw [← Category.assoc, reduced_map_cylinder, Category.assoc, descendApp_cylinder,
        ← Category.assoc, descendApp_cylinder]
      exact congrArg (fun z ↦ z.left) (a.naturality f)
    · exact (Under.w u).trans (Under.w v).symm

private def collapseCode :
    D ⋙ Over.forget Q.code ⟶ (Functor.const I).obj Q.code where
  app p := (D.obj p).hom
  naturality _ _ f := (Over.w (D.map f)).trans (Category.comp_id _).symm

private def augmentationUnder : NecklaceCylinderJointDiagram.cylinderUnder ⟶
    CategoryTheory.Prod.fst NecklaceCode SimplexCategory ⋙ BoundaryNecklaceComma.necklaceUnder where
  app p := Under.homMk (NecklaceCylinderAugmentation.augmentation p.1 p.2)
    (NecklaceCylinderAugmentation.augmentation_boundary p.1 p.2)
  naturality _ _ g :=
    Under.UnderMorphism.ext (NecklaceCylinderJointDiagram.augmentation.naturality g)

/-- The native map into the original fixed target is the whole augmentation
followed by the specified over-target collapse. -/
def native : reduced Q D time ⟶
    (Functor.const I).obj (BoundaryNecklaceComma.necklaceUnder.obj Q.code) :=
  Functor.whiskerLeft (joint Q D time) augmentationUnder ≫
    Functor.whiskerRight (collapseCode Q D) BoundaryNecklaceComma.necklaceUnder

/-- Both projections of a descended product map have the same raw image. -/
theorem pair_square (p : I) :
    (descend Q D time labels a ha).app p ≫ (underCocone W x y).app (labels.obj p) =
      (native Q D time).app p ≫ JTTargetCommaPullback.targetMap W x y Q := by
  let u := (descend Q D time labels a ha).app p ≫ (underCocone W x y).app (labels.obj p)
  let v := (native Q D time).app p ≫ JTTargetCommaPullback.targetMap W x y Q
  change u = v
  apply Under.UnderMorphism.ext
  apply (isPushout (code Q D p) (time.obj p)).hom_ext
  · change (cylinder (code Q D p)).app (time.obj p) ≫
      ((descendApp Q D time labels a ha p).right ≫ ((underCocone W x y).app (labels.obj p)).right) =
      (cylinder (code Q D p)).app (time.obj p) ≫
        (NecklaceCylinderAugmentation.augmentation (code Q D p) (time.obj p) ≫
          (D.obj p).hom.map) ≫ Q.map
    rw [← Category.assoc, descendApp_cylinder, ← Category.assoc, ← Category.assoc,
      NecklaceCylinderAugmentation.augmentation_cylinder]
    exact Over.w (a.app p)
  · exact (Under.w u).trans (Under.w v).symm

private abbrev E := JTTargetCommaPullback.diagram W x y Q
private abbrev nativeTarget := BoundaryNecklaceComma.necklaceUnder.obj Q.code
private abbrev raw := JTConeMappingPresentation.targetUnder (Raw W) (rawVertex W x) (rawVertex W y)

private def firstProjection : labels ⋙ E Q ⟶ labels ⋙ underDiagram W x y where
  app p := JTTargetCommaPullback.fst W x y Q (labels.obj p)
  naturality _ _ f := JTTargetCommaPullback.map_fst W x y Q (labels.map f)

private def secondProjection : labels ⋙ E Q ⟶ (Functor.const I).obj (nativeTarget Q) where
  app p := JTTargetCommaPullback.snd W x y Q (labels.obj p)
  naturality _ _ f :=
    (JTTargetCommaPullback.map_snd W x y Q (labels.map f)).trans (Category.comp_id _).symm

private def rawProjection : labels ⋙ underDiagram W x y ⟶ (Functor.const I).obj
    (raw (W := W) (x := x) (y := y)) :=
  Functor.whiskerLeft labels (underCocone W x y)

private def targetMap : (Functor.const I).obj (nativeTarget Q) ⟶ (Functor.const I).obj
    (raw (W := W) (x := x) (y := y)) :=
  (Functor.const I).map (JTTargetCommaPullback.targetMap W x y Q)

private theorem pullbacks (p : I) :
    IsPullback ((firstProjection Q labels).app p) ((secondProjection Q labels).app p)
      ((rawProjection labels).app p) ((targetMap (I := I) Q).app p) :=
  IsPullback.of_hasPullback ((underCocone W x y).app (labels.obj p))
    (JTTargetCommaPullback.targetMap W x y Q)

/-- Compatible decorated and native natural transformations lift to the literal
fixed-target pullback diagram, for any family of reduced cylinders. -/
def liftFromProjections (F : I ⥤ Under B)
    (decoratedLeg : F ⟶ labels ⋙ underDiagram W x y)
    (nativeLeg : F ⟶ (Functor.const I).obj (nativeTarget Q))
    (compatibility : ∀ p,
      decoratedLeg.app p ≫ (underCocone W x y).app (labels.obj p) =
        nativeLeg.app p ≫ JTTargetCommaPullback.targetMap W x y Q) :
    F ⟶ labels ⋙ E Q :=
  JTPointwisePullbackLift.lift (firstProjection Q labels) (secondProjection Q labels)
    (rawProjection labels) (targetMap (I := I) Q) (pullbacks Q labels)
    decoratedLeg nativeLeg compatibility

/-- The first projection of the fixed-target lift is the decorated leg. -/
theorem liftFromProjections_fst (F : I ⥤ Under B)
    (decoratedLeg : F ⟶ labels ⋙ underDiagram W x y)
    (nativeLeg : F ⟶ (Functor.const I).obj (nativeTarget Q))
    (compatibility : ∀ p,
      decoratedLeg.app p ≫ (underCocone W x y).app (labels.obj p) =
        nativeLeg.app p ≫ JTTargetCommaPullback.targetMap W x y Q)
    (p : I) :
    (liftFromProjections Q labels F decoratedLeg nativeLeg compatibility).app p ≫
      JTTargetCommaPullback.fst W x y Q (labels.obj p) = decoratedLeg.app p :=
  JTPointwisePullbackLift.lift_fst (firstProjection Q labels) (secondProjection Q labels)
    (rawProjection labels) (targetMap (I := I) Q) (pullbacks Q labels)
    decoratedLeg nativeLeg compatibility p

/-- The second projection of the fixed-target lift is the native leg. -/
theorem liftFromProjections_snd (F : I ⥤ Under B)
    (decoratedLeg : F ⟶ labels ⋙ underDiagram W x y)
    (nativeLeg : F ⟶ (Functor.const I).obj (nativeTarget Q))
    (compatibility : ∀ p,
      decoratedLeg.app p ≫ (underCocone W x y).app (labels.obj p) =
        nativeLeg.app p ≫ JTTargetCommaPullback.targetMap W x y Q)
    (p : I) :
    (liftFromProjections Q labels F decoratedLeg nativeLeg compatibility).app p ≫
      JTTargetCommaPullback.snd W x y Q (labels.obj p) = nativeLeg.app p :=
  JTPointwisePullbackLift.lift_snd (firstProjection Q labels) (secondProjection Q labels)
    (rawProjection labels) (targetMap (I := I) Q) (pullbacks Q labels)
    decoratedLeg nativeLeg compatibility p

/-- Evaluate every internal necklace of an arbitrary compatible family into
the original fixed-target comma category. -/
def evaluateFromProjections (F : I ⥤ Under B)
    (decoratedLeg : F ⟶ labels ⋙ underDiagram W x y)
    (nativeLeg : F ⟶ (Functor.const I).obj (nativeTarget Q))
    (compatibility : ∀ p,
      decoratedLeg.app p ≫ (underCocone W x y).app (labels.obj p) =
        nativeLeg.app p ≫ JTTargetCommaPullback.targetMap W x y Q) :
    BoundaryNecklaceComma.Presentation F ⥤ JTGraphFactoredPresentation.TargetComma Q :=
  JTBoundaryNecklacePresentationCone.mapPresentation (E Q) F labels
    (liftFromProjections Q labels F decoratedLeg nativeLeg compatibility) ⋙
      JTTargetCommaExactEvaluation.fromPresentation W x y Q

/-- The evaluated decorated traversal is the specified decorated leg. -/
theorem evaluateFromProjections_decorated (F : I ⥤ Under B)
    (decoratedLeg : F ⟶ labels ⋙ underDiagram W x y)
    (nativeLeg : F ⟶ (Functor.const I).obj (nativeTarget Q))
    (compatibility : ∀ p,
      decoratedLeg.app p ≫ (underCocone W x y).app (labels.obj p) =
        nativeLeg.app p ≫ JTTargetCommaPullback.targetMap W x y Q)
    (P : BoundaryNecklaceComma.Presentation F) :
    ((evaluateFromProjections Q labels F decoratedLeg nativeLeg compatibility).obj P).left.fiber.hom =
      P.fiber.hom ≫ decoratedLeg.app P.base := by
  dsimp only [evaluateFromProjections, CategoryTheory.Functor.comp_obj]
  rw [JTTargetCommaExactEvaluation.decorated_map_obj]
  change (P.fiber.hom ≫
    (liftFromProjections Q labels F decoratedLeg nativeLeg compatibility).app P.base) ≫
      JTTargetCommaPullback.fst W x y Q (labels.obj P.base) = _
  rw [Category.assoc, liftFromProjections_fst]

/-- The evaluated native map to the fixed target is the specified native leg. -/
theorem evaluateFromProjections_native (F : I ⥤ Under B)
    (decoratedLeg : F ⟶ labels ⋙ underDiagram W x y)
    (nativeLeg : F ⟶ (Functor.const I).obj (nativeTarget Q))
    (compatibility : ∀ p,
      decoratedLeg.app p ≫ (underCocone W x y).app (labels.obj p) =
        nativeLeg.app p ≫ JTTargetCommaPullback.targetMap W x y Q)
    (P : BoundaryNecklaceComma.Presentation F) :
    BoundaryNecklaceComma.necklaceUnder.map
        ((evaluateFromProjections Q labels F decoratedLeg nativeLeg compatibility).obj P).hom.hom =
      P.fiber.hom ≫ nativeLeg.app P.base := by
  dsimp only [evaluateFromProjections, CategoryTheory.Functor.comp_obj]
  rw [JTTargetCommaExactEvaluation.native_map_obj]
  change (P.fiber.hom ≫
    (liftFromProjections Q labels F decoratedLeg nativeLeg compatibility).app P.base) ≫
      JTTargetCommaPullback.snd W x y Q (labels.obj P.base) = _
  rw [Category.assoc, liftFromProjections_snd]

/-- The descended family lifts to the literal fixed-target pullbacks. -/
def lift : reduced Q D time ⟶ labels ⋙ E Q :=
  JTPointwisePullbackLift.lift (firstProjection Q labels) (secondProjection Q labels)
    (rawProjection labels) (targetMap (I := I) Q) (pullbacks Q labels)
    (descend Q D time labels a ha) (native Q D time) (pair_square Q D time labels a ha)

theorem lift_fst (p : I) : (lift Q D time labels a ha).app p ≫
    JTTargetCommaPullback.fst W x y Q (labels.obj p) = (descend Q D time labels a ha).app p :=
  JTPointwisePullbackLift.lift_fst (firstProjection Q labels) (secondProjection Q labels)
    (rawProjection labels) (targetMap (I := I) Q) (pullbacks Q labels)
    (descend Q D time labels a ha) (native Q D time) (pair_square Q D time labels a ha) p

theorem lift_snd (p : I) : (lift Q D time labels a ha).app p ≫
    JTTargetCommaPullback.snd W x y Q (labels.obj p) = (native Q D time).app p :=
  JTPointwisePullbackLift.lift_snd (firstProjection Q labels) (secondProjection Q labels)
    (rawProjection labels) (targetMap (I := I) Q) (pullbacks Q labels)
    (descend Q D time labels a ha) (native Q D time) (pair_square Q D time labels a ha) p

/-- Evaluate all the internal necklaces of the descended family into the original comma. -/
def evaluate : BoundaryNecklaceComma.Presentation (reduced Q D time) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTBoundaryNecklacePresentationCone.mapPresentation (E Q) (reduced Q D time) labels
    (lift Q D time labels a ha) ⋙ JTTargetCommaExactEvaluation.fromPresentation W x y Q

/-- The evaluated decorated traversal uses the original internal necklace map. -/
theorem evaluate_decorated (P : BoundaryNecklaceComma.Presentation (reduced Q D time)) :
    ((evaluate Q D time labels a ha).obj P).left.fiber.hom =
      P.fiber.hom ≫ (descend Q D time labels a ha).app P.base := by
  dsimp only [evaluate, CategoryTheory.Functor.comp_obj]
  rw [JTTargetCommaExactEvaluation.decorated_map_obj]
  change (P.fiber.hom ≫ (lift Q D time labels a ha).app P.base) ≫
    JTTargetCommaPullback.fst W x y Q (labels.obj P.base) = _
  rw [Category.assoc, lift_fst]

/-- The evaluated comparison has exactly the specified native map. -/
theorem evaluate_native (P : BoundaryNecklaceComma.Presentation (reduced Q D time)) :
    BoundaryNecklaceComma.necklaceUnder.map ((evaluate Q D time labels a ha).obj P).hom.hom =
      P.fiber.hom ≫ (native Q D time).app P.base := by
  dsimp only [evaluate, CategoryTheory.Functor.comp_obj]
  rw [JTTargetCommaExactEvaluation.native_map_obj]
  change (P.fiber.hom ≫ (lift Q D time labels a ha).app P.base) ≫
    JTTargetCommaPullback.snd W x y Q (labels.obj P.base) = _
  rw [Category.assoc, lift_snd]


section Postcomposition

open BoundaryNecklaceComma (Presentation sourceCode necklaceUnder)
open JTBoundaryNecklacePresentationCone (mapPresentation mapPresentation_code)

private def compareLabels {L : Type} [SmallCategory L]
    (F : I ⥤ Under B) (G : L ⥤ Under B) {b b' : I ⥤ L} (u : b ⟶ b')
    (m : F ⟶ b ⋙ G) (m' : F ⟶ b' ⋙ G)
    (h : ∀ i, m.app i ≫ G.map (u.app i) = m'.app i) :
    mapPresentation G F b m ⟶ mapPresentation G F b' m' where
  app P := ⟨u.app P.base, CostructuredArrow.homMk (𝟙 P.fiber.left) (by
    change necklaceUnder.map (𝟙 P.fiber.left) ≫ (P.fiber.hom ≫ m'.app P.base) =
      (P.fiber.hom ≫ m.app P.base) ≫ G.map (u.app P.base)
    rw [necklaceUnder.map_id, Category.id_comp, Category.assoc, h])⟩
  naturality {P P'} f := by
    apply JTTargetCommaPullback.operator_ext
    · exact u.naturality f.base
    · change (sourceCode G).map (_ ≫ _) = (sourceCode G).map (_ ≫ _)
      rw [(sourceCode G).map_comp, (sourceCode G).map_comp,
        mapPresentation_code, mapPresentation_code]
      change f.fiber.left ≫ 𝟙 _ = 𝟙 _ ≫ f.fiber.left
      rw [Category.comp_id, Category.id_comp]

variable {labels' : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable (u : labels ⟶ labels')
variable (a' : wholeRaw J time Q D ⟶ labels' ⋙ JTDecoratedCylinderOverMapping.rawTarget W x y)
variable (ha' : BoundaryEquation Q D time labels' a')
variable (h : ∀ p, (a.app p).left ≫ ((underDiagram W x y).map (u.app p)).right =
  (a'.app p).left)

include h in
theorem descend_postcomp (p : I) :
    (descend Q D time labels a ha).app p ≫ (underDiagram W x y).map (u.app p) =
      (descend Q D time labels' a' ha').app p := by
  let f := (descend Q D time labels a ha).app p ≫ (underDiagram W x y).map (u.app p)
  let g := (descend Q D time labels' a' ha').app p
  change f = g
  apply Under.UnderMorphism.ext
  apply (isPushout (code Q D p) (time.obj p)).hom_ext
  · change (cylinder (code Q D p)).app (time.obj p) ≫
        ((descendApp Q D time labels a ha p).right ≫
          ((underDiagram W x y).map (u.app p)).right) =
      (cylinder (code Q D p)).app (time.obj p) ≫
        (descendApp Q D time labels' a' ha' p).right
    rw [← Category.assoc, descendApp_cylinder, descendApp_cylinder]
    exact h p
  · exact (Under.w f).trans (Under.w g).symm

include h in
theorem lift_postcomp (p : I) :
    (lift Q D time labels a ha).app p ≫ (E Q).map (u.app p) =
      (lift Q D time labels' a' ha').app p := by
  apply (pullbacks Q labels' p).hom_ext
  · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q (labels'.obj p) =
      _ ≫ JTTargetCommaPullback.fst W x y Q (labels'.obj p)
    rw [Category.assoc, JTTargetCommaPullback.map_fst, ← Category.assoc, lift_fst, lift_fst]
    exact descend_postcomp Q D time labels a ha u a' ha' h p
  · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q (labels'.obj p) =
      _ ≫ JTTargetCommaPullback.snd W x y Q (labels'.obj p)
    rw [Category.assoc, JTTargetCommaPullback.map_snd, lift_snd, lift_snd]

/-- A compatible change of decorated labels compares the actual evaluations. -/
def evaluate_postcomp :
    evaluate Q D time labels a ha ⟶ evaluate Q D time labels' a' ha' :=
  Functor.whiskerRight
    (compareLabels (reduced Q D time) (E Q) u (lift Q D time labels a ha)
      (lift Q D time labels' a' ha') (lift_postcomp Q D time labels a ha u a' ha' h))
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

end Postcomposition

section Gluing

open JTDecoratedIntervalDiagram (leftRaw rightRaw overlapLeft overlapRight glue glue_outerBoundary)
open JTDecoratedIntervalMapping (firstLeft lastRight cylinderFirst cylinderLast)

variable (j : JTTargetJointMarks.Joint Q.code)

private abbrev decorated := labels ⋙ JTDecoratedCylinderOverMapping.rawTarget W x y

/-- Glue and evaluate two coherent decorated families over the entire overlap
with the prescribed outer endpoints. All inner necklaces are retained. -/
def evaluateGlue
    (l : leftRaw J time Q D j ⟶ decorated labels)
    (r : rightRaw J time Q D j ⟶ decorated labels)
    (h : overlapLeft J time Q D j ≫ l = overlapRight J time Q D j ≫ r)
    (hL : ∀ p : I,
      (firstLeft (D.obj p) j ⊗ₘ 𝟙 (J.obj (time.obj p))) ≫ (l.app p).left =
        fst (Δ[0] : SSet.{0}) (J.obj (time.obj p)) ≫ cylinderFirst W x y (labels.obj p))
    (hR : ∀ p : I,
      (lastRight (D.obj p) j ⊗ₘ 𝟙 (J.obj (time.obj p))) ≫ (r.app p).left =
        fst (Δ[0] : SSet.{0}) (J.obj (time.obj p)) ≫ cylinderLast W x y (labels.obj p)) :
    BoundaryNecklaceComma.Presentation (reduced Q D time) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  evaluate Q D time labels (glue J time Q D j labels l r h)
    (fun p ↦ glue_outerBoundary time Q D j labels l r h hL hR p)

end Gluing

end
end DaggerModels.PartII.JTDecoratedIntervalCylinder
