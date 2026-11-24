import DaggerModelsPartII.JTActualJointChainSeamGraph
import DaggerModelsPartII.JTWhiskeredGraphRawTransport
import DaggerModelsPartII.JTChosenSeamSupportedParameterRaw
import DaggerModelsPartII.JTJointPaddedOverlapEvaluation
import DaggerModelsPartII.JTWhiskeredGraphRaw
import DaggerModelsPartII.JTWhiskeredGraphEvaluation
import DaggerModelsPartII.JTGraphCoveredProductInterface

/-!
The exact original-Q raw equations for the whole actual seam graph. The two
outer equations transport the original Family raw equation. The middle uses
its original full-time endpoint support, then the entire coefficient inverse
image; no chain-degree Family or natural parameter section is introduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointChainSeamRaw

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map i) W

private theorem inverseImage_pair {X B C T : SSet.{0}}
    (π : X ⟶ B ⊗ T) (i : C ⟶ B) :
    pullback.fst (π ≫ fst B T) i ≫ π =
      lift (pullback.snd (π ≫ fst B T) i ≫ i)
        (pullback.fst (π ≫ fst B T) i ≫ π ≫ snd B T) := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using
      (pullback.condition : pullback.fst (π ≫ fst B T) i ≫ (π ≫ fst B T) =
        pullback.snd (π ≫ fst B T) i ≫ i)
  · simp only [Category.assoc, lift_snd]

private theorem piece_parameter {X B C S : SSet.{0}} {k l t : SimplexCategory}
    (π : X ⟶ B ⊗ J.obj t) (θ : X ⟶ J.obj k) (n : B ⟶ C)
    (oldθ : C ⊗ J.obj t ⟶ J.obj l) (α : k ⟶ l)
    (hθ : θ ≫ J.map α = π ≫ ((n ⊗ₘ 𝟙 (J.obj t)) ≫ oldθ))
    (i : S ⟶ B) (iOld : S ⟶ C) (hi : i ≫ n = iOld) :
    (pullback.fst (π ≫ fst B (J.obj t)) i ≫ θ) ≫ J.map α =
      lift (pullback.snd (π ≫ fst B (J.obj t)) i ≫ iOld)
        (pullback.fst (π ≫ fst B (J.obj t)) i ≫ π ≫ snd B (J.obj t)) ≫ oldθ := by
  calc
    _ = (pullback.fst (π ≫ fst B (J.obj t)) i ≫ π) ≫
          (n ⊗ₘ 𝟙 (J.obj t)) ≫ oldθ := by
      rw [Category.assoc, hθ]
      simp only [Category.assoc]
    _ = lift (pullback.snd (π ≫ fst B (J.obj t)) i ≫ i)
          (pullback.fst (π ≫ fst B (J.obj t)) i ≫ π ≫ snd B (J.obj t)) ≫
            (n ⊗ₘ 𝟙 (J.obj t)) ≫ oldθ := by rw [inverseImage_pair]
    _ = _ := by
      rw [← Category.assoc, lift_map]
      simp only [Category.assoc, hi, Category.comp_id]

private theorem family_ordered_raw {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (a : C) {X : SSet.{0}}
    (h : X ⟶ ((codes G.labels).obj a).toSSet) (θ : X ⟶ J.obj (K.obj a))
    (g : ((codes G.labels).obj a).toSSet ⟶ Raw W)
    (H : JTWhiskeredGraphRaw.PieceEquations W (G.data a) h θ g) :
    lift h θ ≫ realizedLabel ((codes G.labels).obj a).toSSet W
      ((JTParametrizedTargetFamilyComparison.degrees G.labels).obj a)
      (JTRealizedLabelEndpoints.orderedLabel W x y ((codes G.labels).obj a)
        ((JTParametrizedTargetFamilyComparison.degrees G.labels).obj a)
        (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
          (G.labels.obj a))) = h ≫ g :=
  JTWhiskeredGraphRaw.PieceEquations.ordered_raw W (G.data a) H

private def familyEvaluation {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (time : C ⥤ SimplexCategory)
    (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTWhiskeredGraphEvaluation.productDiagram Q G time c)
    (θ : Y ⟶ K ⋙ J)
    (H : ∀ a : C, JTWhiskeredGraphRaw.PieceEquations W (G.data a)
      (JTWhiskeredGraphEvaluation.nativeCoordinate Q G time c π a)
      (θ.app a) (JTWhiskeredGraphEvaluation.rawTarget Q G c a)) :
    BoundaryNecklaceComma.Presentation
        (JTWhiskeredGraphEvaluation.reduced Q G time c π) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  JTWhiskeredGraphEvaluation.evaluation Q G time c π θ H

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChainSeamChoices.Index F j
private abbrev chain (p : I F j) :=
  (JTActualJointChainSeamChoices.toOriginal F j).obj p
private abbrev marked (p : I F j) :=
  (JTActualJointChainSeamData.marked F j).obj (chain F j p)
private abbrev old (p : I F j) := (JTActualJointChainSeamNative.original F j).obj p
private abbrev v (p : I F j) := (marked F j p).2.val
private abbrev hv (p : I F j) := (marked F j p).2.property
private abbrev oldCode (p : I F j) := (codes L).obj (old F j p)
private abbrev leftCode (p : I F j) := cutLeft (oldCode F j p) (v F j p)
private abbrev rightCode (p : I F j) := cutRight (oldCode F j p) (v F j p)
private abbrev newCode (p : I F j) :=
  wedge (leftCode F j p) (wedge (single 2) (rightCode F j p))
private abbrev data (p : I F j) :=
  (JTActualJointChainSeamNative.seamFamily F j).triangle.data p
private abbrev degree (p : I F j) := (JTActualJointChainSeamChoices.ordinals F j).obj p
private abbrev oldDegree (p : I F j) :=
  (JTActualJointChainSeamNative.oldDegrees F j).obj p
private abbrev φ (p : I F j) :=
  (JTActualJointChainSeamNative.coefficientProjection F j).app p
private abbrev β (p : I F j) := (JTActualJointChainSeamChoices.toOld F j).app p
private abbrev α (p : I F j) :=
  (JTActualJointChoiceChainGraph.toOriginal F j).app (chain F j p)
private abbrev graph : I F j ⥤ SSet.{0} := JTActualJointChainSeamGraph.graph F j
private abbrev π (p : I F j) : (graph F j).obj p ⟶
    (newCode F j p).toSSet ⊗ J.obj (time.obj (old F j p)) :=
  (JTActualJointChainSeamGraph.projection F j).app p
private abbrev θ (p : I F j) : (graph F j).obj p ⟶ J.obj (degree F j p) :=
  (JTActualJointChainSeamGraph.parameter F j).app p
private abbrev native (p : I F j) : (graph F j).obj p ⟶ (newCode F j p).toSSet :=
  π F j p ≫ fst (newCode F j p).toSSet (J.obj (time.obj (old F j p)))
private abbrev clock (p : I F j) :
    (graph F j).obj p ⟶ J.obj (time.obj (old F j p)) :=
  π F j p ≫ snd (newCode F j p).toSSet (J.obj (time.obj (old F j p)))
private abbrev assembly (p : I F j) : newCode F j p ⟶ oldCode F j p :=
  (JTActualJointChainSeamNative.wholeNative F j).app p
private abbrev rawTarget (p : I F j) : (newCode F j p).toSSet ⟶ Raw W :=
  ((JTActualJointChainSeamNative.triangleTarget F j).app p).map ≫ Q.map
private abbrev oldRawTarget (p : I F j) : (oldCode F j p).toSSet ⟶ Raw W :=
  (F.collapse.app (old F j p)).map ≫ Q.map
private abbrev leftInclusion (p : I F j) :
    (leftCode F j p).toSSet ⟶ (newCode F j p).toSSet :=
  tripleRightT (leftCode F j p) (single 2) (rightCode F j p)
private abbrev middleInclusion (p : I F j) :
    (single 2).toSSet ⟶ (newCode F j p).toSSet :=
  tripleRightU (leftCode F j p) (single 2) (rightCode F j p)
private abbrev rightInclusion (p : I F j) :
    (rightCode F j p).toSSet ⟶ (newCode F j p).toSSet :=
  tripleRightV (leftCode F j p) (single 2) (rightCode F j p)
private abbrev middleFirst (p : I F j) :=
  pullback.fst (native F j p) (middleInclusion F j p)
private abbrev middleSecond (p : I F j) :=
  pullback.snd (native F j p) (middleInclusion F j p)

private theorem parameter_piece (p : I F j) {S : NecklaceCode}
    (i : S.toSSet ⟶ (newCode F j p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode F j p).toSSet)
    (hi : i ≫ (assembly F j p).map = iOld) :
    (pullback.fst (native F j p) i ≫ θ F j p) ≫ J.map (φ F j p) =
      lift (pullback.snd (native F j p) i ≫ iOld)
        (pullback.fst (native F j p) i ≫ clock F j p) ≫ F.parameter (old F j p) :=
  piece_parameter (π F j p) (θ F j p) (assembly F j p).map
    (F.parameter (old F j p)) (φ F j p)
    (JTActualJointChainSeamGraph.parameter_projection_app F j p) i iOld hi

private theorem target_piece (p : I F j) {S : NecklaceCode}
    (i : S.toSSet ⟶ (newCode F j p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode F j p).toSSet)
    (hi : i ≫ (assembly F j p).map = iOld) :
    i ≫ rawTarget F j p = iOld ≫ oldRawTarget F j p := by
  change i ≫ ((assembly F j p).map ≫ (F.collapse.app (old F j p)).map) ≫ Q.map = _
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ oldRawTarget F j p) hi

private theorem original_raw (p : I F j) :
    lift (fst (oldCode F j p).toSSet (J.obj (time.obj (old F j p))))
        (F.parameter (old F j p)) ≫
      realizedLabel (oldCode F j p).toSSet W (oldDegree F j p)
        (SSet.yonedaEquiv (JTActualJointCutPrism.originalCoefficient
          (L := L) (old F j p))) =
    fst (oldCode F j p).toSSet (J.obj (time.obj (old F j p))) ≫ oldRawTarget F j p := by
  simpa only [JTComposedPrismLabels.rawProduct, JTBinaryPrismRealization.realizeProduct,
    Category.assoc] using JTActualJointCutPrism.original_raw F (old F j p)

private theorem outer_raw (p : I F j) {S : NecklaceCode}
    (i : S.toSSet ⟶ (newCode F j p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode F j p).toSSet)
    (hi : i ≫ (assembly F j p).map = iOld)
    (d : std.obj (degree F j p) ⟶ TripleBeadEndpointLabel.labels W S)
    (hd : d = std.map (φ F j p) ≫
      JTActualJointCutPrism.originalCoefficient (L := L) (old F j p) ≫ pre W iOld) :
    lift (pullback.snd (native F j p) i)
      (pullback.fst (native F j p) i ≫ θ F j p) ≫
        realizedLabel S.toSSet W (degree F j p) (SSet.yonedaEquiv d) =
      pullback.snd (native F j p) i ≫ i ≫ rawTarget F j p := by
  have hr := JTWhiskeredGraphRawTransport.raw W
    (fst (oldCode F j p).toSSet (J.obj (time.obj (old F j p))))
    (F.parameter (old F j p))
    (JTActualJointCutPrism.originalCoefficient (L := L) (old F j p))
    (oldRawTarget F j p) (original_raw F j p)
    (pullback.snd (native F j p) i) (pullback.fst (native F j p) i ≫ θ F j p)
    (lift (pullback.snd (native F j p) i ≫ iOld)
      (pullback.fst (native F j p) i ≫ clock F j p))
    iOld (φ F j p) d hd (lift_fst _ _) (parameter_piece F j p i iOld hi)
  exact hr.trans (by
    simpa only [Category.assoc] using
      congrArg (fun f ↦ pullback.snd (native F j p) i ≫ f)
        (target_piece F j p i iOld hi).symm)

private abbrev oldSupport (p : I F j) :=
  (JTExactlyMarkedSourceDiagram.supports F j).obj (marked F j p)
private abbrev oldInclusion (p : I F j) :=
  (JTExactlyMarkedSourceDiagram.incl F j).app (marked F j p)
private abbrev oldSupportParameter (p : I F j) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F (old F j p) j
    (JTActualSourceJointSupport.liftedOverlapVertex F (old F j p) j (v F j p) (hv F j p))
private abbrev middleOldFactor (p : I F j) :=
  lift (middleSecond F j p ≫ term (single 2).toSSet)
    (middleFirst F j p ≫ clock F j p) ≫ oldSupportParameter F j p
private abbrev middleChainParameter (p : I F j) :=
  (middleFirst F j p ≫ θ F j p) ≫ J.map (β F j p)

private theorem middle_old_factor (p : I F j) :
    middleChainParameter F j p ≫ J.map (α F j p) =
      middleOldFactor F j p ≫ J.map (oldInclusion F j p) := by
  have hp := parameter_piece F j p (middleInclusion F j p)
    (term (single 2).toSSet ≫ pointAt (oldCode F j p) (ULift.up (v F j p)))
    (JTActualJointChainSeamNative.wholeNative_middle F j p)
  have hp' : middleChainParameter F j p ≫ J.map (α F j p) =
      lift (middleSecond F j p ≫ term (single 2).toSSet ≫
        pointAt (oldCode F j p) (ULift.up (v F j p)))
        (middleFirst F j p ≫ clock F j p) ≫ F.parameter (old F j p) := by
    simpa only [middleChainParameter, φ, JTActualJointChainSeamNative.coefficientProjection,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc] using hp
  calc
    _ = lift (middleSecond F j p ≫ term (single 2).toSSet ≫
          pointAt (oldCode F j p) (ULift.up (v F j p)))
          (middleFirst F j p ≫ clock F j p) ≫ F.parameter (old F j p) := hp'
    _ = lift (middleSecond F j p ≫ term (single 2).toSSet)
          (middleFirst F j p ≫ clock F j p) ≫
            JTActualSourceJointSupport.timeParameter F (old F j p) (v F j p) := by
      simp only [JTActualSourceJointSupport.timeParameter, ← Category.assoc, lift_map,
        Category.comp_id]
    _ = _ := by
      simpa only [middleOldFactor, Category.assoc] using
        congrArg (fun t ↦ lift (middleSecond F j p ≫ term (single 2).toSSet)
          (middleFirst F j p ≫ clock F j p) ≫ t)
          (JTActualSourceJointSupport.timeParameter_factor F (old F j p) j
            (v F j p) (hv F j p)).symm

private def middleSupportParameter (p : I F j) :
    pullback (native F j p) (middleInclusion F j p) ⟶
      J.obj ((JTActualJointChainSeamData.support F j).obj (chain F j p)) :=
  JTOrdinalFaceParameterPullback.factor (oldInclusion F j p) (α F j p)
    (JTActualJointChoiceChainGraph.toOriginal_surjective F j (chain F j p))
    (middleChainParameter F j p) (middleOldFactor F j p) (middle_old_factor F j p)

private theorem middle_support_factor (p : I F j) :
    (middleFirst F j p ≫ θ F j p) ≫ J.map (β F j p) =
      middleSupportParameter F j p ≫
        J.map ((JTActualJointChainSeamData.incl F j).app (chain F j p)) := by
  exact (JTOrdinalFaceParameterPullback.factor_incl
    (oldInclusion F j p) (α F j p)
    (JTActualJointChoiceChainGraph.toOriginal_surjective F j (chain F j p))
    (middleChainParameter F j p) (middleOldFactor F j p) (middle_old_factor F j p)).symm

private theorem middle_target_raw (p : I F j) :
    middleInclusion F j p ≫ rawTarget F j p =
      term (single 2).toSSet ≫ SSet.yonedaEquiv.symm
        (rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) := by
  have hp : pointAt (oldCode F j p) (ULift.up (v F j p)) ≫
      (F.collapse.app (old F j p)).map = pointAt Q.code (ULift.up j.val) := by
    rw [pointAt_comp]
    exact congrArg (pointAt Q.code) (ULift.ext _ _ (hv F j p))
  have hj : SSet.yonedaEquiv.symm
      (rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) =
        pointAt Q.code (ULift.up j.val) ≫ Q.map :=
    JTJointPaddedOverlapEvaluation.target_map (W := W) (Q := Q) j
  calc
    _ = (term (single 2).toSSet ≫ pointAt (oldCode F j p) (ULift.up (v F j p))) ≫
          oldRawTarget F j p :=
      target_piece F j p (middleInclusion F j p)
        (term (single 2).toSSet ≫ pointAt (oldCode F j p) (ULift.up (v F j p)))
        (JTActualJointChainSeamNative.wholeNative_middle F j p)
    _ = term (single 2).toSSet ≫ (pointAt Q.code (ULift.up j.val) ≫ Q.map) := by
      simpa only [oldRawTarget, Category.assoc] using
        congrArg (fun f ↦ term (single 2).toSSet ≫ f ≫ Q.map) hp
    _ = _ := congrArg (fun f ↦ term (single 2).toSSet ≫ f) hj.symm

private theorem middle_raw (p : I F j) :
    lift (middleSecond F j p) (middleFirst F j p ≫ θ F j p) ≫
      realizedLabel (single 2).toSSet W (degree F j p)
        (SSet.yonedaEquiv (data F j p).middle) =
      middleSecond F j p ≫ middleInclusion F j p ≫ rawTarget F j p := by
  let d := (JTActualJointChainSeamData.support F j).obj (chain F j p)
  let u := (JTActualJointChainSeamData.incl F j).app (chain F j p)
  have hu : Function.Injective u.toOrderHom :=
    SimplexCategory.mono_iff_injective.mp
      (JTActualJointChainSeamData.incl_mono F j (chain F j p))
  have ha : std.map u = 𝟙 (std.obj d) ≫
      (JTActualJointChainSeamData.supportIncl F j).app (chain F j p) :=
    (Category.id_comp _).symm
  have hr := JTChosenSeamSupportedParameterRaw.graph_raw_of_old_factor
    W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (JTActualJointChainSeamData.supportSSet F j)
    (JTActualJointChoiceChainGraph.ordinals F j)
    (JTActualJointChainSeamData.supportIncl F j)
    (JTActualJointChainSeamData.endpointRows F j)
    (JTActualJointChoiceChainGraph.chainEnding F j)
    (JTActualJointChoiceChainGraph.chainStarting F j)
    (JTActualJointChainSeamData.ending_boundary F j)
    (JTActualJointChainSeamData.starting_boundary F j)
    (JTActualJointChainSeamData.supported_endpoint F j)
    (JTActualJointChainSeamData.ending_supported F j)
    (JTActualJointChainSeamData.starting_supported F j)
    p d u hu (𝟙 (std.obj d)) ha (middleSecond F j p)
    (middleFirst F j p ≫ θ F j p) (middleSupportParameter F j p)
    (middle_support_factor F j p)
  rw [JTActualJointChainSeamNative.triangle_middle]
  exact hr.trans (by
    simpa only [Category.assoc] using
      congrArg (fun f ↦ middleSecond F j p ≫ f) (middle_target_raw F j p).symm)

/-- Exact raw equations on all three FULL native inverse images of the actual
seam graph, with the complete original time and the original fixed target Q. -/
theorem pieceEquations (p : I F j) :
    JTWhiskeredGraphRaw.PieceEquations W (data F j p)
      (native F j p) (θ F j p) (rawTarget F j p) := by
  refine ⟨?_, middle_raw F j p, ?_⟩
  · apply outer_raw F j p (leftInclusion F j p)
      (cutLeftι (oldCode F j p) (v F j p))
      (JTActualJointChainSeamNative.wholeNative_left F j p)
    simpa only [JTActualJointCutPrism.leftCoefficient, Category.assoc] using
      JTActualJointChainSeamNative.triangle_left F j p
  · apply outer_raw F j p (rightInclusion F j p)
      (cutRightι (oldCode F j p) (v F j p))
      (JTActualJointChainSeamNative.wholeNative_right F j p)
    simpa only [JTActualJointCutPrism.rightCoefficient, Category.assoc] using
      JTActualJointChainSeamNative.triangle_right F j p

/-- The whole actual triangle coefficient has the literal original-Q raw value. -/
theorem raw (p : I F j) :
    lift (native F j p) (θ F j p) ≫
      realizedLabel (newCode F j p).toSSet W (degree F j p)
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients (data F j p)))) =
      native F j p ≫ rawTarget F j p :=
  JTWhiskeredGraphRaw.PieceEquations.raw W (data F j p) (pieceEquations F j p)

/-- The whole raw equality is for the actual ordered label, hence is the
original fixed-target evaluation input on every complete graph component. -/
theorem ordered_raw (p : I F j) :
    lift (native F j p) (θ F j p) ≫
      realizedLabel
        (((codes (JTActualJointChainSeamNative.seamFamily F j).triangle.labels).obj p).toSSet)
        W ((JTParametrizedTargetFamilyComparison.degrees
          (JTActualJointChainSeamNative.seamFamily F j).triangle.labels).obj p)
        (JTRealizedLabelEndpoints.orderedLabel W x y
          ((codes (JTActualJointChainSeamNative.seamFamily F j).triangle.labels).obj p)
          ((JTParametrizedTargetFamilyComparison.degrees
            (JTActualJointChainSeamNative.seamFamily F j).triangle.labels).obj p)
          (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            ((JTActualJointChainSeamNative.seamFamily F j).triangle.labels.obj p))) =
      native F j p ≫ rawTarget F j p :=
  family_ordered_raw (JTActualJointChainSeamNative.seamFamily F j).triangle p
    (native F j p) (θ F j p) (rawTarget F j p) (pieceEquations F j p)

/-- The same whole graph, typed over the original fixed-Q native/time product. -/
def projectionTarget : graph F j ⟶
    JTWhiskeredGraphEvaluation.productDiagram Q
      (JTActualJointChainSeamNative.seamFamily F j).triangle
      (JTActualJointChainSeamGraph.oldTime F j)
      (JTActualJointChainSeamNative.triangleTarget F j) :=
  JTActualJointChainSeamGraph.projection F j ≫
    (JTGraphCoveredProductInterface.iso
      (codes (JTActualJointChainSeamNative.seamFamily F j).triangle.labels)
      (JTActualJointChainSeamGraph.oldTime F j) Q.code Q.map
      (JTActualJointChainSeamNative.triangleTarget F j)).hom

private theorem projectionTarget_app (p : I F j) :
    ((projectionTarget F j).app p : (graph F j).obj p ⟶
        (newCode F j p).toSSet ⊗ J.obj (time.obj (old F j p))) = π F j p := by
  simp only [projectionTarget, NatTrans.comp_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id]

private theorem evaluationPieces (p : I F j) :
    JTWhiskeredGraphRaw.PieceEquations W (data F j p)
      (JTWhiskeredGraphEvaluation.nativeCoordinate Q
        (JTActualJointChainSeamNative.seamFamily F j).triangle
        (JTActualJointChainSeamGraph.oldTime F j)
        (JTActualJointChainSeamNative.triangleTarget F j) (projectionTarget F j) p)
      (θ F j p)
      (JTWhiskeredGraphEvaluation.rawTarget Q
        (JTActualJointChainSeamNative.seamFamily F j).triangle
        (JTActualJointChainSeamNative.triangleTarget F j) p) := by
  change JTWhiskeredGraphRaw.PieceEquations W (data F j p)
    ((projectionTarget F j).app p ≫ fst _ _) (θ F j p) (rawTarget F j p)
  rw [projectionTarget_app]
  exact pieceEquations F j p

/-- The full inverse image of both original endpoint lines is collapsed. -/
abbrev reduced := JTWhiskeredGraphEvaluation.reduced Q
  (JTActualJointChainSeamNative.seamFamily F j).triangle
  (JTActualJointChainSeamGraph.oldTime F j)
  (JTActualJointChainSeamNative.triangleTarget F j) (projectionTarget F j)

/-- Evaluate every internal necklace of the whole actual seam in the SAME Q. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  familyEvaluation Q (JTActualJointChainSeamNative.seamFamily F j).triangle
    (JTActualJointChainSeamGraph.oldTime F j)
    (JTActualJointChainSeamNative.triangleTarget F j) (projectionTarget F j)
    (JTActualJointChainSeamGraph.parameter F j) (evaluationPieces F j)

/-- Forget the complete presentation to its actual triangle-choice source. -/
abbrev toChoices : BoundaryNecklaceComma.Presentation (reduced F j) ⥤ I F j :=
  JTWhiskeredGraphEvaluation.toOriginal Q
    (JTActualJointChainSeamNative.seamFamily F j).triangle
    (JTActualJointChainSeamGraph.oldTime F j)
    (JTActualJointChainSeamNative.triangleTarget F j) (projectionTarget F j)

/-- All full-graph presentations give a weak cover of the actual triangle choices. -/
theorem toChoices_weak : WeakEquivalence (nerveMap (toChoices F j)) := by
  apply JTWhiskeredGraphEvaluation.toOriginal_weak Q
    (JTActualJointChainSeamNative.seamFamily F j).triangle
    (JTActualJointChainSeamGraph.oldTime F j)
    (JTActualJointChainSeamNative.triangleTarget F j) (projectionTarget F j)
  intro p
  rw [projectionTarget_app]
  exact JTActualJointChainSeamGraph.projection_trivialFibration F j p


end
end DaggerModels.PartII.JTActualJointChainSeamRaw
