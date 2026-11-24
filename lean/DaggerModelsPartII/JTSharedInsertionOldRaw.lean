import DaggerModelsPartII.JTSharedInsertionOldGraph
import DaggerModelsPartII.JTSharedInsertionOuterRaw
import DaggerModelsPartII.JTWhiskeredGraphRawTransport
import DaggerModelsPartII.JTWhiskeredGraphEvaluation

/-!
# Complete original-Q evaluation of the actual corrected old split

Both old corrected surroundings retain their complete original intervals and
outer correction pairs. The old point coefficient is the original varying row
at b, reindexed along the shared chain; its raw equation is the point restriction
of the original Family raw equation. All coefficient lifts, original time and
internal necklaces are retained, without a chain-degree product Family or section.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionOldRaw

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)
open JTSharedInsertionOldGraph (graph projection parameter oldFamily oldTime originalBase)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map i) W

private def firstCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ fst B T
private def secondCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ snd B T

private def inverseImage {X B S : SSet.{0}} (h : X ⟶ B) (i : S ⟶ B) : SSet.{0} :=
  pullback h i

private def inverseFirst {X B S : SSet.{0}} (h : X ⟶ B) (i : S ⟶ B) :
    inverseImage h i ⟶ X := pullback.fst h i

private def inverseSecond {X B S : SSet.{0}} (h : X ⟶ B) (i : S ⟶ B) :
    inverseImage h i ⟶ S := pullback.snd h i

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

private theorem piece_parameter_sealed {X B C S : SSet.{0}} {k l t : SimplexCategory}
    (π : X ⟶ B ⊗ J.obj t) (θ : X ⟶ J.obj k) (n : B ⟶ C)
    (oldθ : C ⊗ J.obj t ⟶ J.obj l) (α : k ⟶ l)
    (hθ : θ ≫ J.map α = π ≫ ((n ⊗ₘ 𝟙 (J.obj t)) ≫ oldθ))
    (i : S ⟶ B) (iOld : S ⟶ C) (hi : i ≫ n = iOld) :
    (inverseFirst (firstCoordinate π) i ≫ θ) ≫ J.map α =
      lift (inverseSecond (firstCoordinate π) i ≫ iOld)
        (inverseFirst (firstCoordinate π) i ≫ secondCoordinate π) ≫ oldθ :=
  piece_parameter π θ n oldθ α hθ i iOld hi

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

private def familyLift {C : Type} [SmallCategory C]
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
    JTWhiskeredGraphEvaluation.reduced Q G time c π ⟶
      G.labels ⋙ JTTargetCommaPullback.diagram W x y Q :=
  JTWhiskeredGraphEvaluation.pullbackLift Q G time c π θ H

private def productProjection {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) (U : NecklaceCode)
    {B : SSet.{0}} (q : U.toSSet ⟶ B) (c : N ⟶ (Functor.const C).obj U)
    {Y : C ⥤ SSet.{0}} (π : Y ⟶ JTGraphCoveredProductInterface.product N t) :=
  π ≫ (JTGraphCoveredProductInterface.iso N t U q c).hom

private theorem productProjection_app {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) (U : NecklaceCode)
    {B : SSet.{0}} (q : U.toSSet ⟶ B) (c : N ⟶ (Functor.const C).obj U)
    {Y : C ⥤ SSet.{0}} (π : Y ⟶ JTGraphCoveredProductInterface.product N t) (a : C) :
    ((productProjection N t U q c π).app a :
      Y.obj a ⟶ (N.obj a).toSSet ⊗ J.obj (t.obj a)) = π.app a := by
  rw [productProjection, NatTrans.comp_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id]

private theorem familyPieces {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (time : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) time)
    (θ : Y ⟶ K ⋙ J)
    (H : ∀ a : C, JTWhiskeredGraphRaw.PieceEquations W (G.data a)
      (firstCoordinate (π.app a)) (θ.app a) ((c.app a).map ≫ Q.map)) (a : C) :
    JTWhiskeredGraphRaw.PieceEquations W (G.data a)
      (JTWhiskeredGraphEvaluation.nativeCoordinate Q G time c
        (productProjection (codes G.labels) time Q.code Q.map c π) a)
      (θ.app a) (JTWhiskeredGraphEvaluation.rawTarget Q G c a) := by
  change JTWhiskeredGraphRaw.PieceEquations W (G.data a)
    ((productProjection (codes G.labels) time Q.code Q.map c π).app a ≫ fst _ _)
    (θ.app a) ((c.app a).map ≫ Q.map)
  rw [productProjection_app]
  exact H a

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev I := JTSharedInsertionOldGraph.Index F j
private abbrev old (p : I F j) := (originalBase F j).obj p
private abbrev marked (p : I F j) := (JTSharedInsertionChainSupport.marks F j 1).obj p
private abbrev v (p : I F j) := (marked F j p).2.val
private abbrev oldCode (p : I F j) := (codes L).obj (old F j p)
private abbrev leftCode (p : I F j) := (JTSharedInsertionSeamSurroundings.leftNative F j).obj p
private abbrev rightCode (p : I F j) := (JTSharedInsertionSeamSurroundings.rightNative F j).obj p
private abbrev newCode (p : I F j) := wedge (leftCode F j p) (wedge (single 0) (rightCode F j p))
private abbrev data (p : I F j) := (oldFamily F j).data p
private abbrev degree (p : I F j) := (JTSharedInsertionChoices.ordinals F j).obj p
private abbrev α (p : I F j) := (JTSharedInsertionChoices.toOriginal F j).app p
private def π (p : I F j) : (graph F j).obj p ⟶
    (newCode F j p).toSSet ⊗ J.obj (time.obj (old F j p)) := (projection F j).app p
private def θ (p : I F j) : (graph F j).obj p ⟶ J.obj (degree F j p) := (parameter F j).app p
private def native (p : I F j) : (graph F j).obj p ⟶ (newCode F j p).toSSet :=
  firstCoordinate (π F j p)
private def clock (p : I F j) : (graph F j).obj p ⟶ J.obj (time.obj (old F j p)) :=
  secondCoordinate (π F j p)
private abbrev assembly (p : I F j) := (JTSharedInsertionSeamNative.oldAssembly F j).app p
private abbrev rawTarget (p : I F j) :=
  ((JTSharedInsertionOldGraph.target F j).app p).map ≫ Q.map
private abbrev oldTarget (p : I F j) := (F.collapse.app (old F j p)).map ≫ Q.map
private abbrev leftInclusion (p : I F j) :=
  tripleRightT (leftCode F j p) (single 0) (rightCode F j p)
private abbrev middleInclusion (p : I F j) :=
  tripleRightU (leftCode F j p) (single 0) (rightCode F j p)
private abbrev rightInclusion (p : I F j) :=
  tripleRightV (leftCode F j p) (single 0) (rightCode F j p)
private abbrev pointNative (p : I F j) :=
  term (single 0).toSSet ≫ pointAt (oldCode F j p) (ULift.up (v F j p))

private theorem projected_parameter (p : I F j) :
    θ F j p ≫ J.map (α F j p) = π F j p ≫
      (((assembly F j p).map ⊗ₘ 𝟙 (J.obj (time.obj (old F j p)))) ≫
        F.parameter (old F j p)) :=
  JTSharedInsertionOldGraph.parameter_projection_app F j p

private theorem parameter_piece (p : I F j) {S : NecklaceCode}
    (i : S.toSSet ⟶ (newCode F j p).toSSet) (n : S.toSSet ⟶ (oldCode F j p).toSSet)
    (hi : i ≫ (assembly F j p).map = n) :
    (inverseFirst (native F j p) i ≫ θ F j p) ≫ J.map (α F j p) =
      lift (inverseSecond (native F j p) i ≫ n)
        (inverseFirst (native F j p) i ≫ clock F j p) ≫ F.parameter (old F j p) :=
  piece_parameter_sealed (π F j p) (θ F j p) (assembly F j p).map (F.parameter (old F j p))
    (α F j p) (projected_parameter F j p) i n hi

private theorem target_piece (p : I F j) {S : NecklaceCode}
    (i : S.toSSet ⟶ (newCode F j p).toSSet) (n : S.toSSet ⟶ (oldCode F j p).toSSet)
    (hi : i ≫ (assembly F j p).map = n) :
    i ≫ rawTarget F j p = n ≫ oldTarget F j p := by
  simpa only [rawTarget, JTSharedInsertionOldGraph.target, NatTrans.comp_app,
    Functor.whiskerLeft_app, oldTarget, Category.assoc] using
      congrArg (fun f ↦ f ≫ (F.collapse.app (old F j p)).map ≫ Q.map) hi

private theorem point_coefficient (a : A) (b : Fin (((codes L).obj a).len + 1)) :
    JTActualSourceJointSupport.oldVertexRow (L := L) a b ≫
        JTNativeRowLabel.labelFromRow W 0 =
      JTActualJointCutPrism.originalCoefficient (L := L) a ≫
        pre W (term (single 0).toSSet ≫ pointAt ((codes L).obj a) (ULift.up b)) := by
  unfold JTActualSourceJointSupport.oldVertexRow JTNativeRowLabel.labelFromRow
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← diagramMappingPrecomp_comp,
    ← ReversalDiscreteFreeColimits.discreteFree.map_comp]
  have h : (singleIso 0).hom = term (single 0).toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]

private theorem middle_coefficient (p : I F j) :
    (data F j p).middle = std.map (α F j p) ≫
      JTActualJointCutPrism.originalCoefficient (L := L) (old F j p) ≫
        pre W (pointNative F j p) := by
  change (std.map (α F j p) ≫
    JTActualSourceJointSupport.oldVertexRow (L := L) (old F j p) (v F j p)) ≫
      JTNativeRowLabel.labelFromRow W 0 = _
  rw [Category.assoc, point_coefficient]

private theorem original_restriction (p : I F j) (S : NecklaceCode)
    (n : S.toSSet ⟶ (oldCode F j p).toSSet) {X : SSet.{0}}
    (h : X ⟶ S.toSSet) (q : X ⟶ J.obj (degree F j p))
    (t : X ⟶ J.obj (time.obj (old F j p)))
    (hq : q ≫ J.map (α F j p) = lift (h ≫ n) t ≫ F.parameter (old F j p)) :
    lift h q ≫ realizedLabel S.toSSet W (degree F j p)
      (SSet.yonedaEquiv (std.map (α F j p) ≫
        JTActualJointCutPrism.originalCoefficient (L := L) (old F j p) ≫ pre W n)) =
      h ≫ n ≫ oldTarget F j p := by
  have hold : lift (fst (oldCode F j p).toSSet (J.obj (time.obj (old F j p))))
      (F.parameter (old F j p)) ≫ realizedLabel (oldCode F j p).toSSet W _
        (SSet.yonedaEquiv (JTActualJointCutPrism.originalCoefficient (L := L) (old F j p))) =
      fst (oldCode F j p).toSSet (J.obj (time.obj (old F j p))) ≫ oldTarget F j p := by
    simpa only [JTComposedPrismLabels.rawProduct, JTBinaryPrismRealization.realizeProduct,
      Category.assoc] using JTActualJointCutPrism.original_raw F (old F j p)
  exact JTWhiskeredGraphRawTransport.raw W _ _ _ _ hold h q (lift (h ≫ n) t)
    n (α F j p) _ rfl (lift_fst _ _) hq

private theorem middle_raw (p : I F j) :
    lift (inverseSecond (native F j p) (middleInclusion F j p))
      (inverseFirst (native F j p) (middleInclusion F j p) ≫ θ F j p) ≫
        realizedLabel (single 0).toSSet W (degree F j p)
          (SSet.yonedaEquiv (data F j p).middle) =
      inverseSecond (native F j p) (middleInclusion F j p) ≫
        middleInclusion F j p ≫ rawTarget F j p := by
  rw [middle_coefficient]
  have h := original_restriction F j p (single 0) (pointNative F j p)
    (inverseSecond (native F j p) (middleInclusion F j p))
    (inverseFirst (native F j p) (middleInclusion F j p) ≫ θ F j p)
    (inverseFirst (native F j p) (middleInclusion F j p) ≫ clock F j p)
    (parameter_piece F j p (middleInclusion F j p) (pointNative F j p)
      (JTSharedInsertionOldGraph.oldAssembly_middle F j p))
  exact h.trans (by
    simpa only [Category.assoc] using congrArg (fun f ↦
      inverseSecond (native F j p) (middleInclusion F j p) ≫ f)
        (target_piece F j p (middleInclusion F j p) (pointNative F j p)
          (JTSharedInsertionOldGraph.oldAssembly_middle F j p)).symm)

private theorem left_raw (p : I F j) :
    lift (inverseSecond (native F j p) (leftInclusion F j p))
      (inverseFirst (native F j p) (leftInclusion F j p) ≫ θ F j p) ≫
        realizedLabel (leftCode F j p).toSSet W (degree F j p)
          (SSet.yonedaEquiv (data F j p).left) =
      inverseSecond (native F j p) (leftInclusion F j p) ≫
        leftInclusion F j p ≫ rawTarget F j p := by
  have h := JTSharedInsertionOuterRaw.left_raw F j p
    (inverseSecond (native F j p) (leftInclusion F j p))
    (inverseFirst (native F j p) (leftInclusion F j p) ≫ θ F j p)
    (inverseFirst (native F j p) (leftInclusion F j p) ≫ clock F j p)
    (parameter_piece F j p (leftInclusion F j p) _
      (JTSharedInsertionOldGraph.oldAssembly_left F j p))
  exact h.trans (by
    simpa only [Category.assoc] using congrArg (fun f ↦
      inverseSecond (native F j p) (leftInclusion F j p) ≫ f)
        (target_piece F j p (leftInclusion F j p) _
          (JTSharedInsertionOldGraph.oldAssembly_left F j p)).symm)

private theorem right_raw (p : I F j) :
    lift (inverseSecond (native F j p) (rightInclusion F j p))
      (inverseFirst (native F j p) (rightInclusion F j p) ≫ θ F j p) ≫
        realizedLabel (rightCode F j p).toSSet W (degree F j p)
          (SSet.yonedaEquiv (data F j p).right) =
      inverseSecond (native F j p) (rightInclusion F j p) ≫
        rightInclusion F j p ≫ rawTarget F j p := by
  have h := JTSharedInsertionOuterRaw.right_raw F j p
    (inverseSecond (native F j p) (rightInclusion F j p))
    (inverseFirst (native F j p) (rightInclusion F j p) ≫ θ F j p)
    (inverseFirst (native F j p) (rightInclusion F j p) ≫ clock F j p)
    (parameter_piece F j p (rightInclusion F j p) _
      (JTSharedInsertionOldGraph.oldAssembly_right F j p))
  exact h.trans (by
    simpa only [Category.assoc] using congrArg (fun f ↦
      inverseSecond (native F j p) (rightInclusion F j p) ≫ f)
        (target_piece F j p (rightInclusion F j p) _
          (JTSharedInsertionOldGraph.oldAssembly_right F j p)).symm)

/-- All three FULL native inverse images satisfy the exact original-Q raw equations. -/
theorem pieceEquations (p : I F j) :
    JTWhiskeredGraphRaw.PieceEquations W (data F j p)
      (native F j p) (θ F j p) (rawTarget F j p) :=
  ⟨left_raw F j p, middle_raw F j p, right_raw F j p⟩

/-- The complete actual corrected old split has its literal original-Q raw value. -/
theorem raw (p : I F j) :
    lift (native F j p) (θ F j p) ≫
      realizedLabel (newCode F j p).toSSet W (degree F j p)
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients (data F j p)))) =
      native F j p ≫ rawTarget F j p :=
  JTWhiskeredGraphRaw.PieceEquations.raw W (data F j p) (pieceEquations F j p)

/-- The same exact whole raw equation for the actual ordered old label. -/
theorem ordered_raw (p : I F j) :
    lift (native F j p) (θ F j p) ≫
      realizedLabel ((codes (oldFamily F j).labels).obj p).toSSet W
        ((JTParametrizedTargetFamilyComparison.degrees (oldFamily F j).labels).obj p)
        (JTRealizedLabelEndpoints.orderedLabel W x y ((codes (oldFamily F j).labels).obj p)
          ((JTParametrizedTargetFamilyComparison.degrees (oldFamily F j).labels).obj p)
          (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            ((oldFamily F j).labels.obj p))) = native F j p ≫ rawTarget F j p :=
  family_ordered_raw (oldFamily F j) p (native F j p) (θ F j p)
    (rawTarget F j p) (pieceEquations F j p)

/-- The whole original-time graph, typed over the same original fixed Q. -/
def projectionTarget : graph F j ⟶ JTWhiskeredGraphEvaluation.productDiagram Q
    (oldFamily F j) (oldTime F j) (JTSharedInsertionOldGraph.target F j) :=
  productProjection (codes (oldFamily F j).labels) (oldTime F j) Q.code Q.map
    (JTSharedInsertionOldGraph.target F j) (projection F j)

private theorem projectionTarget_app (p : I F j) :
    ((projectionTarget F j).app p : (graph F j).obj p ⟶
      (newCode F j p).toSSet ⊗ J.obj (time.obj (old F j p))) = π F j p :=
  productProjection_app (codes (oldFamily F j).labels) (oldTime F j) Q.code Q.map
    (JTSharedInsertionOldGraph.target F j) (projection F j) p

private theorem evaluationPieces (p : I F j) :
    JTWhiskeredGraphRaw.PieceEquations W (data F j p)
      (JTWhiskeredGraphEvaluation.nativeCoordinate Q (oldFamily F j) (oldTime F j)
        (JTSharedInsertionOldGraph.target F j) (projectionTarget F j) p)
      (θ F j p)
      (JTWhiskeredGraphEvaluation.rawTarget Q (oldFamily F j)
        (JTSharedInsertionOldGraph.target F j) p) :=
  familyPieces Q (oldFamily F j) (oldTime F j) (JTSharedInsertionOldGraph.target F j)
    (projection F j) (parameter F j) (pieceEquations F j) p

/-- Collapse the full inverse image of both original endpoint lines. -/
abbrev reduced := JTWhiskeredGraphEvaluation.reduced Q (oldFamily F j) (oldTime F j)
  (JTSharedInsertionOldGraph.target F j) (projectionTarget F j)

/-- The actual whole graph lifts to the literal original fixed-Q pullback diagram. -/
abbrev pullbackLift := familyLift Q (oldFamily F j) (oldTime F j)
  (JTSharedInsertionOldGraph.target F j) (projectionTarget F j)
  (parameter F j) (evaluationPieces F j)

/-- Evaluate ALL internal necklaces of the ACTUAL corrected old split in the same Q. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  familyEvaluation Q (oldFamily F j) (oldTime F j) (JTSharedInsertionOldGraph.target F j)
    (projectionTarget F j) (parameter F j) (evaluationPieces F j)

/-- The full evaluation is exactly the map of complete pullback presentations. -/
theorem evaluation_eq_mapPresentation : evaluation F j =
    JTBoundaryNecklacePresentationCone.mapPresentation (JTTargetCommaPullback.diagram W x y Q)
      (reduced F j) (oldFamily F j).labels (pullbackLift F j) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W x y Q := rfl

/-- Forget the full graph presentation to its actual shared-chain source. -/
abbrev toChoices : BoundaryNecklaceComma.Presentation (reduced F j) ⥤ I F j :=
  JTWhiskeredGraphEvaluation.toOriginal Q (oldFamily F j) (oldTime F j)
    (JTSharedInsertionOldGraph.target F j) (projectionTarget F j)

/-- The full presentation is weak over Shared.Index, without weakening a marked projection. -/
theorem toChoices_weak : WeakEquivalence (nerveMap (toChoices F j)) := by
  apply JTWhiskeredGraphEvaluation.toOriginal_weak Q (oldFamily F j) (oldTime F j)
    (JTSharedInsertionOldGraph.target F j) (projectionTarget F j)
  intro p
  rw [projectionTarget_app]
  exact JTSharedInsertionOldGraph.projection_trivialFibration F j p

end
end DaggerModels.PartII.JTSharedInsertionOldRaw
