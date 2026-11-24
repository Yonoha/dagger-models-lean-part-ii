import DaggerModelsPartII.JTSharedInsertionSeamGraph
import DaggerModelsPartII.JTSharedInsertionOuterRaw
import DaggerModelsPartII.JTWhiskeredGraphRawTransport
import DaggerModelsPartII.JTChosenSeamSupportedParameterRaw
import DaggerModelsPartII.JTJointPaddedOverlapEvaluation
import DaggerModelsPartII.JTWhiskeredGraphRaw
import DaggerModelsPartII.JTWhiskeredGraphEvaluation
import DaggerModelsPartII.JTGraphCoveredProductInterface

/-!
The exact original-Q raw equations for the whole corrected shared seam graph.
Both corrected outer equations retain all old intervals and correction edges. The middle uses
its original full-time endpoint support, then the entire coefficient inverse
image; no chain-degree Family or natural parameter section is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionSeamRaw

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

private def firstCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ fst B T
private def secondCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ snd B T

private def fiber {X Y Z : SSet.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) : SSet.{0} :=
  pullback f g
private def fiberFirst {X Y Z : SSet.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) : fiber f g ⟶ X :=
  pullback.fst f g
private def fiberSecond {X Y Z : SSet.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) : fiber f g ⟶ Y :=
  pullback.snd f g

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
    (fiberFirst (firstCoordinate π) i ≫ θ) ≫ J.map α =
      lift (fiberSecond (firstCoordinate π) i ≫ iOld)
        (fiberFirst (firstCoordinate π) i ≫ secondCoordinate π) ≫ oldθ :=
  piece_parameter π θ n oldθ α hθ i iOld hi

private def familyLeft {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K) (a : C) :
    (P.obj a).toSSet ⟶ ((codes G.labels).obj a).toSSet :=
  tripleRightT (P.obj a) M (R.obj a)

private def familyMiddle {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K) (a : C) :
    M.toSSet ⟶ ((codes G.labels).obj a).toSSet :=
  tripleRightU (P.obj a) M (R.obj a)

private def familyRight {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K) (a : C) :
    (R.obj a).toSSet ⟶ ((codes G.labels).obj a).toSSet :=
  tripleRightV (P.obj a) M (R.obj a)

private def FamilyPieces {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (a : C) {X : SSet.{0}} (h : X ⟶ ((codes G.labels).obj a).toSSet)
    (q : X ⟶ J.obj (K.obj a)) (g : ((codes G.labels).obj a).toSSet ⟶ Raw W) : Prop :=
  JTWhiskeredGraphRaw.PieceEquations W (G.data a) h q g

private theorem family_piece_equations {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (a : C) {X : SSet.{0}} (h : X ⟶ ((codes G.labels).obj a).toSSet)
    (q : X ⟶ J.obj (K.obj a)) (g : ((codes G.labels).obj a).toSSet ⟶ Raw W)
    (hl : lift (fiberSecond h (familyLeft G a)) (fiberFirst h (familyLeft G a) ≫ q) ≫
      realizedLabel (P.obj a).toSSet W (K.obj a) (SSet.yonedaEquiv (G.data a).left) =
        fiberSecond h (familyLeft G a) ≫ familyLeft G a ≫ g)
    (hm : lift (fiberSecond h (familyMiddle G a)) (fiberFirst h (familyMiddle G a) ≫ q) ≫
      realizedLabel M.toSSet W (K.obj a) (SSet.yonedaEquiv (G.data a).middle) =
        fiberSecond h (familyMiddle G a) ≫ familyMiddle G a ≫ g)
    (hr : lift (fiberSecond h (familyRight G a)) (fiberFirst h (familyRight G a) ≫ q) ≫
      realizedLabel (R.obj a).toSSet W (K.obj a) (SSet.yonedaEquiv (G.data a).right) =
        fiberSecond h (familyRight G a) ≫ familyRight G a ≫ g) :
    FamilyPieces G a h q g := ⟨hl, hm, hr⟩

private theorem family_raw {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (a : C) {X : SSet.{0}} (h : X ⟶ ((codes G.labels).obj a).toSSet)
    (q : X ⟶ J.obj (K.obj a)) (g : ((codes G.labels).obj a).toSSet ⟶ Raw W)
    (H : FamilyPieces G a h q g) :
    lift h q ≫ realizedLabel ((codes G.labels).obj a).toSSet W (K.obj a)
      (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients (G.data a)))) = h ≫ g :=
  JTWhiskeredGraphRaw.PieceEquations.raw W (G.data a) H

private theorem family_ordered_raw {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (a : C) {X : SSet.{0}}
    (h : X ⟶ ((codes G.labels).obj a).toSSet) (θ : X ⟶ J.obj (K.obj a))
    (g : ((codes G.labels).obj a).toSSet ⟶ Raw W)
    (H : FamilyPieces G a h θ g) :
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

private def canonical_projection {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product N t) (p : C) :
    Y.obj p ⟶ (N.obj p).toSSet ⊗ J.obj (t.obj p) := π.app p

private def family_projection {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (time : C ⥤ SimplexCategory) {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) time) (p : C) :
    Y.obj p ⟶ (wedge (P.obj p) (wedge M (R.obj p))).toSSet ⊗ J.obj (time.obj p) :=
  π.app p


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
    (H : ∀ a : C, FamilyPieces G a
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

private theorem family_cover_weak {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (time : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) time)
    (H : ∀ a : C, trivialFibrations SSet.{0} (π.app a)) :
    WeakEquivalence (nerveMap (JTWhiskeredGraphEvaluation.toOriginal Q G time c
      (productProjection (codes G.labels) time Q.code Q.map c π))) := by
  apply JTWhiskeredGraphEvaluation.toOriginal_weak Q G time c
    (productProjection (codes G.labels) time Q.code Q.map c π)
  intro a
  rw [productProjection_app (codes G.labels) time Q.code Q.map c π a]
  exact H a

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTSharedInsertionNormalizedSeam.Index F j
private abbrev chain (p : I F j) :=
  (JTSharedInsertionSeamTriangles.toOriginal F j).obj p
private abbrev marked (p : I F j) :=
  (JTSharedInsertionChainSupport.marks F j 1).obj (chain F j p)
private abbrev old (p : I F j) := (JTSharedInsertionNormalizedSeam.original F j).obj p
private abbrev v (p : I F j) := (marked F j p).2.val
private abbrev hv (p : I F j) := (marked F j p).2.property
private abbrev oldCode (p : I F j) := (codes L).obj (old F j p)
private abbrev leftCode (p : I F j) :=
  (JTSharedInsertionSeamSurroundings.leftNative F j).obj (chain F j p)
private abbrev rightCode (p : I F j) :=
  (JTSharedInsertionSeamSurroundings.rightNative F j).obj (chain F j p)
private abbrev newCode (p : I F j) :=
  (codes (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels).obj p
private abbrev data (p : I F j) :=
  (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.data p
private abbrev degree (p : I F j) := (JTSharedInsertionSeamTriangles.ordinals F j).obj p
private abbrev oldDegree (p : I F j) :=
  (JTSharedInsertionNormalizedSeam.oldDegrees F j).obj p
private abbrev φ (p : I F j) :=
  (JTSharedInsertionNormalizedSeam.coefficientProjection F j).app p
private abbrev β (p : I F j) := (JTSharedInsertionSeamTriangles.toOld F j).app p
private abbrev α (p : I F j) :=
  (JTSharedInsertionChoices.toOriginal F j).app (chain F j p)
private abbrev graph : I F j ⥤ SSet.{0} := JTSharedInsertionSeamGraph.graph F j
private def π (p : I F j) :=
  canonical_projection (codes (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels)
    (JTSharedInsertionSeamGraph.oldTime F j) (JTSharedInsertionSeamGraph.projection F j) p
private def θ (p : I F j) : (graph F j).obj p ⟶ J.obj (degree F j p) :=
  (JTSharedInsertionSeamGraph.parameter F j).app p
private def native (p : I F j) : (graph F j).obj p ⟶ (newCode F j p).toSSet :=
  firstCoordinate (π F j p)
private def clock (p : I F j) :
    (graph F j).obj p ⟶ J.obj (time.obj (old F j p)) :=
  secondCoordinate (π F j p)
private abbrev assembly (p : I F j) : newCode F j p ⟶ oldCode F j p :=
  (JTSharedInsertionSeamNative.wholeNative F j).app p
private abbrev rawTarget (p : I F j) : (newCode F j p).toSSet ⟶ Raw W :=
  ((JTSharedInsertionSeamNative.triangleTarget F j).app p).map ≫ Q.map
private abbrev oldRawTarget (p : I F j) : (oldCode F j p).toSSet ⟶ Raw W :=
  (F.collapse.app (old F j p)).map ≫ Q.map
private abbrev leftInclusion (p : I F j) :
    (leftCode F j p).toSSet ⟶ (newCode F j p).toSSet :=
  familyLeft (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle p
private abbrev middleInclusion (p : I F j) :
    (single 2).toSSet ⟶ (newCode F j p).toSSet :=
  familyMiddle (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle p
private abbrev rightInclusion (p : I F j) :
    (rightCode F j p).toSSet ⟶ (newCode F j p).toSSet :=
  familyRight (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle p
private abbrev middleFirst (p : I F j) :=
  fiberFirst (native F j p) (middleInclusion F j p)
private abbrev middleSecond (p : I F j) :=
  fiberSecond (native F j p) (middleInclusion F j p)

set_option maxHeartbeats 850000 in
private theorem projected_parameter (p : I F j) :
    θ F j p ≫ J.map (φ F j p) = π F j p ≫
      (((assembly F j p).map ⊗ₘ 𝟙 (J.obj (time.obj (old F j p)))) ≫
        F.parameter (old F j p)) :=
  JTSharedInsertionSeamGraph.parameter_projection_app F j p

private theorem parameter_piece (p : I F j) {S : NecklaceCode}
    (i : S.toSSet ⟶ (newCode F j p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode F j p).toSSet)
    (hi : i ≫ (assembly F j p).map = iOld) :
    (fiberFirst (native F j p) i ≫ θ F j p) ≫ J.map (φ F j p) =
      lift (fiberSecond (native F j p) i ≫ iOld)
        (fiberFirst (native F j p) i ≫ clock F j p) ≫ F.parameter (old F j p) :=
  piece_parameter_sealed (π F j p) (θ F j p) (assembly F j p).map
    (F.parameter (old F j p)) (φ F j p)
    (projected_parameter F j p) i iOld hi

private theorem target_piece (p : I F j) {S : NecklaceCode}
    (i : S.toSSet ⟶ (newCode F j p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode F j p).toSSet)
    (hi : i ≫ (assembly F j p).map = iOld) :
    i ≫ rawTarget F j p = iOld ≫ oldRawTarget F j p := by
  have ht := NatTrans.congr_app (JTSharedInsertionSeamNative.triangleTarget_whole F j) p
  change i ≫ ((JTSharedInsertionSeamNative.triangleTarget F j).app p).map ≫ Q.map = _
  rw [ht]
  change i ≫ ((assembly F j p).map ≫ (F.collapse.app (old F j p)).map) ≫ Q.map = _
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ oldRawTarget F j p) hi

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
    (JTSharedInsertionSeamGraph.wholeNative_middle F j p)
  have hp' : middleChainParameter F j p ≫ J.map (α F j p) =
      lift (middleSecond F j p ≫ term (single 2).toSSet ≫
        pointAt (oldCode F j p) (ULift.up (v F j p)))
        (middleFirst F j p ≫ clock F j p) ≫ F.parameter (old F j p) := by
    simpa only [middleChainParameter, φ, JTSharedInsertionNormalizedSeam.coefficientProjection,
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

private abbrev hα (p : I F j) :=
  JTSharedInsertionChoices.toOriginal_surjective F j (chain F j p)
private abbrev hu (p : I F j) := SimplexCategory.mono_iff_injective.mp
  (JTExactlyMarkedSourceDiagram.incl_mono F j (marked F j p))
private abbrev middleFace (p : I F j) :=
  JTOrdinalFaceInverseImage.ordinal (oldInclusion F j p) (α F j p)
private abbrev middleFaceIncl (p : I F j) :=
  JTOrdinalFaceInverseImage.incl (oldInclusion F j p) (α F j p) (hα F j p)
private abbrev middleFaceToOld (p : I F j) :=
  JTOrdinalFaceInverseImage.toFace (oldInclusion F j p) (α F j p) (hα F j p) (hu F j p)

private def middleFaceToSupport (p : I F j) :
    std.obj (middleFace F j p) ⟶
      (JTSharedInsertionChainSupport.diagram F j 1).obj (chain F j p) where
  app n x := ⟨(std.map (middleFaceIncl F j p)).app n x, by
    change (std.map (α F j p)).app n
      ((std.map (middleFaceIncl F j p)).app n x) ∈
        (JTIncidentBeadSupportData.support F j (marked F j p)).obj n
    have h : std.map (middleFaceIncl F j p) ≫ std.map (α F j p) =
        (std.map (middleFaceToOld F j p) ≫
          (JTIncidentBeadSupportTransport.vertexToSupport F j).app (marked F j p)) ≫
            (JTIncidentBeadSupportTransport.inclusion F j).app (marked F j p) := by
      have hf := JTOrdinalFaceInverseImage.toFace_fac
        (oldInclusion F j p) (α F j p) (hα F j p) (hu F j p)
      rw [← std.map_comp, ← hf, std.map_comp, Category.assoc]
      congr 1
    have hx := congrFun (NatTrans.congr_app h n) x
    change _ = (((std.map (middleFaceToOld F j p) ≫
      (JTIncidentBeadSupportTransport.vertexToSupport F j).app (marked F j p)).app n x).val)
      at hx
    simp only [SSet.comp_app, types_comp_apply] at hx
    rw [hx]
    exact ((std.map (middleFaceToOld F j p) ≫
      (JTIncidentBeadSupportTransport.vertexToSupport F j).app (marked F j p)).app n x).property⟩
  naturality n m θ := by
    funext x
    apply Subtype.ext
    exact congrFun ((std.map (middleFaceIncl F j p)).naturality θ) x

private theorem middleFaceToSupport_fac (p : I F j) :
    std.map (middleFaceIncl F j p) = middleFaceToSupport F j p ≫
      (JTSharedInsertionChainSupport.inclusion F j 1).app (chain F j p) := rfl

private def middleSupportParameter (p : I F j) :
    fiber (native F j p) (middleInclusion F j p) ⟶ J.obj (middleFace F j p) :=
  JTOrdinalFaceParameterPullback.factor (oldInclusion F j p) (α F j p) (hα F j p)
    (middleChainParameter F j p) (middleOldFactor F j p) (middle_old_factor F j p)

private theorem middle_support_factor (p : I F j) :
    (middleFirst F j p ≫ θ F j p) ≫ J.map (β F j p) =
      middleSupportParameter F j p ≫ J.map (middleFaceIncl F j p) :=
  (JTOrdinalFaceParameterPullback.factor_incl
    (oldInclusion F j p) (α F j p) (hα F j p)
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
        (JTSharedInsertionSeamGraph.wholeNative_middle F j p)
    _ = term (single 2).toSSet ≫ (pointAt Q.code (ULift.up j.val) ≫ Q.map) := by
      simpa only [oldRawTarget, Category.assoc] using
        congrArg (fun f ↦ term (single 2).toSSet ≫ f ≫ Q.map) hp
    _ = _ := congrArg (fun f ↦ term (single 2).toSSet ≫ f) hj.symm

private theorem middle_raw (p : I F j) :
    lift (middleSecond F j p) (middleFirst F j p ≫ θ F j p) ≫
      realizedLabel (single 2).toSSet W (degree F j p)
        (SSet.yonedaEquiv (data F j p).middle) =
      middleSecond F j p ≫ middleInclusion F j p ≫ rawTarget F j p := by
  have hr := JTChosenSeamSupportedParameterRaw.graph_raw_of_old_factor
    W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (JTSharedInsertionChainSupport.diagram F j 1)
    (JTSharedInsertionChoices.ordinals F j)
    (JTSharedInsertionChainSupport.inclusion F j 1)
    (JTSharedInsertionChainSupport.rows F j 1)
    (JTSharedInsertionIncidentEdges.ending F j 1)
    (JTSharedInsertionIncidentEdges.starting F j 1)
    (JTSharedInsertionIncidentEdges.ending_endpoints F j 1)
    (JTSharedInsertionIncidentEdges.starting_endpoints F j 1)
    (JTSharedInsertionChainSupport.row_on_support F j 1)
    (JTSharedInsertionIncidentEdges.ending_on_support F j 1)
    (JTSharedInsertionIncidentEdges.starting_on_support F j 1)
    p (middleFace F j p) (middleFaceIncl F j p)
    (JTOrdinalFaceInverseImage.incl_injective _ _ _)
    (middleFaceToSupport F j p) (middleFaceToSupport_fac F j p)
    (middleSecond F j p) (middleFirst F j p ≫ θ F j p)
    (middleSupportParameter F j p) (middle_support_factor F j p)
  exact hr.trans (by
    simpa only [Category.assoc] using
      congrArg (fun f ↦ middleSecond F j p ≫ f) (middle_target_raw F j p).symm)

private theorem left_target_raw (p : I F j) :
    leftInclusion F j p ≫ rawTarget F j p =
      JTSharedInsertionNativeAssembly.leftToOriginal F j (chain F j p) ≫
        oldRawTarget F j p :=
  target_piece F j p (leftInclusion F j p) _
    (JTSharedInsertionSeamGraph.wholeNative_left F j p)

private theorem right_target_raw (p : I F j) :
    rightInclusion F j p ≫ rawTarget F j p =
      JTSharedInsertionNativeAssembly.rightToOriginal F j (chain F j p) ≫
        oldRawTarget F j p :=
  target_piece F j p (rightInclusion F j p) _
    (JTSharedInsertionSeamGraph.wholeNative_right F j p)

private theorem left_raw (p : I F j) :
    lift (fiberSecond (native F j p) (leftInclusion F j p))
      (fiberFirst (native F j p) (leftInclusion F j p) ≫ θ F j p) ≫
        realizedLabel (leftCode F j p).toSSet W (degree F j p)
          (SSet.yonedaEquiv (data F j p).left) =
      fiberSecond (native F j p) (leftInclusion F j p) ≫
        leftInclusion F j p ≫ rawTarget F j p := by
  let a := fiberFirst (native F j p) (leftInclusion F j p)
  let b := fiberSecond (native F j p) (leftInclusion F j p)
  let n := JTSharedInsertionNativeAssembly.leftToOriginal F j (chain F j p)
  have hp := parameter_piece F j p (leftInclusion F j p) n
    (JTSharedInsertionSeamGraph.wholeNative_left F j p)
  have hp' : ((a ≫ θ F j p) ≫ J.map (β F j p)) ≫ J.map (α F j p) =
      lift (b ≫ n) (a ≫ clock F j p) ≫ F.parameter (old F j p) := by
    simpa only [a, b, φ, JTSharedInsertionNormalizedSeam.coefficientProjection,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc] using hp
  have hr := JTSharedInsertionOuterRaw.left_raw F j (chain F j p) b
    ((a ≫ θ F j p) ≫ J.map (β F j p)) (a ≫ clock F j p) hp'
  have hc : (data F j p).left = std.map (β F j p) ≫
      JTSharedInsertionSeamSurroundings.leftCoefficient F j (chain F j p) := rfl
  rw [hc, ← JTWhiskerEdgeGraphRaw.coefficient_reindex W (β F j p)
    b (a ≫ θ F j p) (JTSharedInsertionSeamSurroundings.leftCoefficient F j (chain F j p))]
  exact hr.trans (by
    simpa only [Category.assoc] using congrArg (fun f ↦ b ≫ f)
      (left_target_raw F j p).symm)

private theorem right_raw (p : I F j) :
    lift (fiberSecond (native F j p) (rightInclusion F j p))
      (fiberFirst (native F j p) (rightInclusion F j p) ≫ θ F j p) ≫
        realizedLabel (rightCode F j p).toSSet W (degree F j p)
          (SSet.yonedaEquiv (data F j p).right) =
      fiberSecond (native F j p) (rightInclusion F j p) ≫
        rightInclusion F j p ≫ rawTarget F j p := by
  let a := fiberFirst (native F j p) (rightInclusion F j p)
  let b := fiberSecond (native F j p) (rightInclusion F j p)
  let n := JTSharedInsertionNativeAssembly.rightToOriginal F j (chain F j p)
  have hp := parameter_piece F j p (rightInclusion F j p) n
    (JTSharedInsertionSeamGraph.wholeNative_right F j p)
  have hp' : ((a ≫ θ F j p) ≫ J.map (β F j p)) ≫ J.map (α F j p) =
      lift (b ≫ n) (a ≫ clock F j p) ≫ F.parameter (old F j p) := by
    simpa only [a, b, φ, JTSharedInsertionNormalizedSeam.coefficientProjection,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc] using hp
  have hr := JTSharedInsertionOuterRaw.right_raw F j (chain F j p) b
    ((a ≫ θ F j p) ≫ J.map (β F j p)) (a ≫ clock F j p) hp'
  have hc : (data F j p).right = std.map (β F j p) ≫
      JTSharedInsertionSeamSurroundings.rightCoefficient F j (chain F j p) := rfl
  rw [hc, ← JTWhiskerEdgeGraphRaw.coefficient_reindex W (β F j p)
    b (a ≫ θ F j p) (JTSharedInsertionSeamSurroundings.rightCoefficient F j (chain F j p))]
  exact hr.trans (by
    simpa only [Category.assoc] using congrArg (fun f ↦ b ≫ f)
      (right_target_raw F j p).symm)

/-- Exact raw equations on all three FULL native inverse images of the actual
seam graph, with the complete original time and the original fixed target Q. -/
theorem pieceEquations (p : I F j) :
    FamilyPieces (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle p
      (native F j p) (θ F j p) (rawTarget F j p) :=
  family_piece_equations (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle p
    (native F j p) (θ F j p) (rawTarget F j p)
    (left_raw F j p) (middle_raw F j p) (right_raw F j p)

/-- The whole actual triangle coefficient has the literal original-Q raw value. -/
theorem raw (p : I F j) :
    lift (native F j p) (θ F j p) ≫
      realizedLabel (newCode F j p).toSSet W (degree F j p)
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients (data F j p)))) =
      native F j p ≫ rawTarget F j p :=
  family_raw (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle p
    (native F j p) (θ F j p) (rawTarget F j p) (pieceEquations F j p)

/-- The whole raw equality is for the actual ordered label, hence is the
original fixed-target evaluation input on every complete graph component. -/
theorem ordered_raw (p : I F j) :
    lift (native F j p) (θ F j p) ≫
      realizedLabel
        (((codes (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels).obj p).toSSet)
        W ((JTParametrizedTargetFamilyComparison.degrees
          (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels).obj p)
        (JTRealizedLabelEndpoints.orderedLabel W x y
          ((codes (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels).obj p)
          ((JTParametrizedTargetFamilyComparison.degrees
            (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels).obj p)
          (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            ((JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels.obj p))) =
      native F j p ≫ rawTarget F j p :=
  family_ordered_raw (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle p
    (native F j p) (θ F j p) (rawTarget F j p) (pieceEquations F j p)

/-- The same whole graph, typed over the original fixed-Q native/time product. -/
def projectionTarget : graph F j ⟶
    JTWhiskeredGraphEvaluation.productDiagram Q
      (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
      (JTSharedInsertionSeamGraph.oldTime F j)
      (JTSharedInsertionSeamNative.triangleTarget F j) :=
  productProjection (codes (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels)
    (JTSharedInsertionSeamGraph.oldTime F j) Q.code Q.map
    (JTSharedInsertionSeamNative.triangleTarget F j) (JTSharedInsertionSeamGraph.projection F j)

private theorem evaluationPieces (p : I F j) :
    JTWhiskeredGraphRaw.PieceEquations W (data F j p)
      (JTWhiskeredGraphEvaluation.nativeCoordinate Q
        (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
        (JTSharedInsertionSeamGraph.oldTime F j)
        (JTSharedInsertionSeamNative.triangleTarget F j) (projectionTarget F j) p)
      (θ F j p)
      (JTWhiskeredGraphEvaluation.rawTarget Q
        (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
        (JTSharedInsertionSeamNative.triangleTarget F j) p) :=
  familyPieces Q (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
    (JTSharedInsertionSeamGraph.oldTime F j) (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionSeamGraph.projection F j) (JTSharedInsertionSeamGraph.parameter F j)
    (pieceEquations F j) p

/-- The full inverse image of both original endpoint lines is collapsed. -/
abbrev reduced := JTWhiskeredGraphEvaluation.reduced Q
  (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
  (JTSharedInsertionSeamGraph.oldTime F j)
  (JTSharedInsertionSeamNative.triangleTarget F j) (projectionTarget F j)

/-- Evaluate every internal necklace of the whole actual seam in the SAME Q. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  familyEvaluation Q (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
    (JTSharedInsertionSeamGraph.oldTime F j)
    (JTSharedInsertionSeamNative.triangleTarget F j) (projectionTarget F j)
    (JTSharedInsertionSeamGraph.parameter F j) (evaluationPieces F j)

/-- Forget the complete presentation to its actual triangle-choice source. -/
abbrev toChoices : BoundaryNecklaceComma.Presentation (reduced F j) ⥤ I F j :=
  JTWhiskeredGraphEvaluation.toOriginal Q
    (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
    (JTSharedInsertionSeamGraph.oldTime F j)
    (JTSharedInsertionSeamNative.triangleTarget F j) (projectionTarget F j)

/-- All full-graph presentations give a weak cover of the actual triangle choices. -/
theorem toChoices_weak : WeakEquivalence (nerveMap (toChoices F j)) :=
  family_cover_weak Q (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle
    (JTSharedInsertionSeamGraph.oldTime F j) (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionSeamGraph.projection F j)
    (JTSharedInsertionSeamGraph.projection_trivialFibration F j)

end
end DaggerModels.PartII.JTSharedInsertionSeamRaw
