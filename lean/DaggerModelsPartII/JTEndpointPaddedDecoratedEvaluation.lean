import DaggerModelsPartII.JTEndpointPaddedDecoratedFamily
import DaggerModelsPartII.JTNativeEndpointPaddingPresentation
import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange

/-! Compare the fully padded evaluation with the original fixed-target evaluation. -/

set_option autoImplicit false
set_option maxHeartbeats 135000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTEndpointPaddedDecoratedFamily

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family codes liftNatural evaluate)
open JTParametrizedTargetLiftTransport (graph graph_square)
open DecoratedCylinderNecklacePresentation (underDiagram)
open NecklaceCylinderAugmentation (augmentation)
open JTBoundaryNecklacePresentationTransport (comparisonWithSourceChange)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Index (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time)

private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev oldCode (a : A) := (codes L).obj a
private abbrev D := JTTargetCommaPullback.diagram W x y Q

private abbrev J := GroupoidSimplex.parameter

private abbrev sourceMap :=
  JTNativeEndpointPadding.collapseCylinders (codes L) time

private theorem componentOperator (a : A) :
    (sourceMap (L := L) (time := time)).app a =
      NecklaceCylinderJointDiagram.cylinderUnder.map
        (show ((codes (labels L)).obj a, time.obj a) ⟶ ((codes L).obj a, time.obj a)
          from ((pr.map ((collapseLabels L).app a)).1, 𝟙 (time.obj a))) := rfl

private theorem componentCollapse (a : A) :
    (pr.map ((collapseLabels L).app a)).1 ≫ F.collapse.app a =
      (family F).collapse.app a := rfl

set_option maxHeartbeats 100000 in
private theorem componentParameter (a : A) :
    ((pr.map ((collapseLabels L).app a)).1.map ⊗ₘ J.map (𝟙 (time.obj a))) ≫ F.parameter a =
      (family F).parameter a ≫ J.map (pr.map ((collapseLabels L).app a)).2 :=
  collapseParameter F a

private abbrev sourceCode (a : A) := (codes (labels L)).obj a
private abbrev d' (a : A) := (family F).collapse.app a
private abbrev d (a : A) := F.collapse.app a

set_option maxHeartbeats 180000 in
private theorem decoratedComponent (a : A) :
    graph ((family F).parameter a) ≫ (underDiagram W x y).map ((collapseLabels L).app a) =
      (sourceMap (L := L) (time := time)).app a ≫ graph (F.parameter a) := by
  rw [componentOperator]
  exact graph_square ((collapseLabels L).app a) (𝟙 (time.obj a))
    ((family F).parameter a) (F.parameter a) (componentParameter F a)

private theorem pasteNative {X Y T U V : SSet.{0}}
    (s : X ⟶ Y) (u : X ⟶ T) (v : Y ⟶ U) (c : T ⟶ U)
    (d₀ : T ⟶ V) (d₁ : U ⟶ V)
    (h₀ : s ≫ v = u ≫ c) (h₁ : c ≫ d₁ = d₀) : u ≫ d₀ = s ≫ (v ≫ d₁) := by
  rw [← h₁, ← Category.assoc, ← h₀, Category.assoc]

set_option maxHeartbeats 180000 in
private theorem nativeComponent (a : A) :
    JTCylinderOverTarget.native W x y Q (sourceCode (L := L) a) (time.obj a) (d' F a) =
      (sourceMap (L := L) (time := time)).app a ≫
        JTCylinderOverTarget.native W x y Q (oldCode (L := L) a) (time.obj a) (d F a) := by
  apply Under.UnderMorphism.ext
  let c := (pr.map ((collapseLabels L).app a)).1
  let k := time.obj a
  let z : (sourceCode (L := L) a, k) ⟶ (oldCode (L := L) a, k) := (c, 𝟙 k)
  let u := (sourceMap (L := L) (time := time)).app a
  let h : u.right ≫ augmentation (oldCode (L := L) a) k =
      augmentation (sourceCode (L := L) a) k ≫ c.map :=
    NecklaceCylinderJointDiagram.augmentation.naturality z
  let h' : c.map ≫ (d F a).map = (d' F a).map :=
    congrArg (fun s : sourceCode (L := L) a ⟶ Q.code ↦ s.map) (componentCollapse F a)
  exact pasteNative u.right _ _ c.map (d' F a).map (d F a).map h h'

private theorem familyLift_fst {K : A ⥤ Index W x y} (H : Family Q K time) (a : A) :
    (liftNatural H).app a ≫ JTTargetCommaPullback.fst W x y Q (K.obj a) =
      graph (H.parameter a) :=
  JTCylinderOverTarget.lift_decorated W x y Q (K.obj a) ((codes K).obj a) (time.obj a)
    (graph (H.parameter a)) (H.collapse.app a) (H.raw a)

private theorem familyLift_snd {K : A ⥤ Index W x y} (H : Family Q K time) (a : A) :
    (liftNatural H).app a ≫ JTTargetCommaPullback.snd W x y Q (K.obj a) =
      JTCylinderOverTarget.native W x y Q ((codes K).obj a) (time.obj a) (H.collapse.app a) :=
  JTCylinderOverTarget.lift_native W x y Q (K.obj a) ((codes K).obj a) (time.obj a)
    (graph (H.parameter a)) (H.collapse.app a) (H.raw a)

private abbrev leftLift (a : A) := (liftNatural (family F)).app a ≫
  (D (Q := Q)).map ((collapseLabels L).app a)
private abbrev rightLift (a : A) := (sourceMap (L := L) (time := time)).app a ≫
  (liftNatural F).app a

private theorem compareFst (a : A) :
    leftLift F a ≫ JTTargetCommaPullback.fst W x y Q (L.obj a) =
      rightLift F a ≫ JTTargetCommaPullback.fst W x y Q (L.obj a) := by
  unfold leftLift rightLift
  rw [Category.assoc, JTTargetCommaPullback.map_fst, ← Category.assoc,
    familyLift_fst, Category.assoc, familyLift_fst]
  exact decoratedComponent F a

private theorem compareSnd (a : A) :
    leftLift F a ≫ JTTargetCommaPullback.snd W x y Q (L.obj a) =
      rightLift F a ≫ JTTargetCommaPullback.snd W x y Q (L.obj a) := by
  unfold leftLift rightLift
  rw [Category.assoc, JTTargetCommaPullback.map_snd, familyLift_snd,
    Category.assoc, familyLift_snd]
  exact nativeComponent F a

/-- Both fixed-target pullback projections commute with the padded label collapse. -/
theorem compareLifts (a : A) : leftLift F a = rightLift F a :=
  pullback.hom_ext (compareFst F a) (compareSnd F a)

/-- Compare every internal necklace after projecting its padded cylinder and label together. -/
def compareEvaluation :
    evaluate (family F) ⟶ JTNativeEndpointPadding.projectPresentation (codes L) time ⋙ evaluate F := by
  exact comparisonWithSourceChange (D (Q := Q)) (liftNatural (family F)) (liftNatural F)
    (sourceMap (L := L) (time := time)) (collapseLabels L) (compareLifts F)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

end

end DaggerModels.PartII.JTEndpointPaddedDecoratedFamily
