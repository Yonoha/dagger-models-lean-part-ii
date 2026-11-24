import DaggerModelsPartII.JTSharedInsertionTriangleGraphBridge
import DaggerModelsPartII.JTSharedInsertionSeamRaw
import DaggerModelsPartII.JTGraphCoveredRawTransport

/-!
# Actual corrected phase evaluations in the same original Q

The common triangle graph is identified with the checked full original-time
triangle graph. Actual detour and long comparisons then pull its ordered raw
map back through their complete all-lifts graph maps. Both endpoint inverse
images and every internal necklace are retained by the existing graph-covered
evaluation construction. No product Family, parameter section, caller raw or
support premise is introduced. The collapsed phase is handled separately.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionPhaseRaw

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private def firstCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ fst B T

private theorem timeMap_app {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (n : N ⟶ M) (t : C ⥤ SimplexCategory) (a : C) :
    (JTSharedInsertionPhaseGraph.mapWithTime n t).app a =
      (n.app a).map ⊗ₘ 𝟙 (J.obj (t.obj a)) := rfl

private theorem native_square {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (t : C ⥤ SimplexCategory)
    {Y Z : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product N t)
    (π' : Z ⟶ JTGraphCoveredProductInterface.product M t)
    (η : Y ⟶ Z) (n : N ⟶ M)
    (hp : η ≫ π' = π ≫ JTSharedInsertionPhaseGraph.mapWithTime n t) (a : C) :
    firstCoordinate (π.app a) ≫ (n.app a).map =
      η.app a ≫ firstCoordinate (π'.app a) := by
  have h := congrArg (fun f ↦ f ≫ fst (M.obj a).toSSet (J.obj (t.obj a)))
    (NatTrans.congr_app hp a)
  simpa only [NatTrans.comp_app, timeMap_app, Category.assoc, tensorHom_fst,
    firstCoordinate] using h.symm

private def RawAt {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (a : C) {X : SSet.{0}} (h : X ⟶ ((codes G.labels).obj a).toSSet)
    (q : X ⟶ J.obj (K.obj a)) (g : ((codes G.labels).obj a).toSSet ⟶ Raw W) : Prop :=
  lift h q ≫ realizedLabel ((codes G.labels).obj a).toSSet W (K.obj a)
      (JTRealizedLabelEndpoints.orderedLabel W x y ((codes G.labels).obj a) (K.obj a)
        (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
          (G.labels.obj a))) = h ≫ g

private def RawDiagram {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (θ : Y ⟶ K ⋙ J) : Prop :=
  ∀ a : C, RawAt G a (firstCoordinate (π.app a)) (θ.app a) ((c.app a).map ≫ Q.map)

private theorem pull_domain {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y Z : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (π' : Z ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (θ : Y ⟶ K ⋙ J) (θ' : Z ⟶ K ⋙ J) (η : Y ⟶ Z)
    (hp : η ≫ π' = π) (hq : η ≫ θ' = θ)
    (H : RawDiagram Q G t c π' θ') : RawDiagram Q G t c π θ := by
  intro a
  have hn : η.app a ≫ firstCoordinate (π'.app a) = firstCoordinate (π.app a) := by
    simpa only [NatTrans.comp_app, firstCoordinate, Category.assoc] using
      congrArg (fun f ↦ f ≫ fst _ _) (NatTrans.congr_app hp a)
  have ht : η.app a ≫ θ'.app a = θ.app a := NatTrans.congr_app hq a
  have h := H a
  change lift _ _ ≫ _ = _ at h ⊢
  calc
    _ = η.app a ≫ (lift (firstCoordinate (π'.app a)) (θ'.app a) ≫ _) := by
      rw [← hn, ← ht, ← comp_lift, Category.assoc]
    _ = η.app a ≫ (firstCoordinate (π'.app a) ≫ _) := congrArg (η.app a ≫ ·) h
    _ = _ := by rw [← Category.assoc, hn]

private theorem pull_arrow {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R P' R' : C ⥤ NecklaceCode}
    {K : C ⥤ SimplexCategory} {M N : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (H : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) N P' R' K)
    (t : C ⥤ SimplexCategory)
    (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    (c' : codes H.labels ⟶ (Functor.const C).obj Q.code)
    {Y Z : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (π' : Z ⟶ JTGraphCoveredProductInterface.product (codes H.labels) t)
    (θ : Y ⟶ K ⋙ J) (θ' : Z ⟶ K ⋙ J)
    (f : G.labels ⟶ H.labels) (η : Y ⟶ Z)
    (hp : η ≫ π' = π ≫ JTSharedInsertionPhaseGraph.mapWithTime
      (JTWhiskeredSeamTarget.nativeOf f) t)
    (hq : η ≫ θ' = θ)
    (hd : ∀ a : C, ((pr W x y).map (f.app a)).2 = 𝟙 (K.obj a))
    (hc : JTWhiskeredSeamTarget.nativeOf f ≫ c' = c)
    (hr : RawDiagram Q H t c' π' θ') : RawDiagram Q G t c π θ := by
  intro a
  have hn := native_square t π π' η (JTWhiskeredSeamTarget.nativeOf f) hp a
  rw [JTWhiskeredSeamTarget.nativeOf_app] at hn
  have hθ : θ.app a ≫ J.map ((pr W x y).map (f.app a)).2 = η.app a ≫ θ'.app a := by
    rw [hd a, J.map_id]
    change θ.app a = η.app a ≫ θ'.app a
    exact (NatTrans.congr_app hq a).symm
  have h := JTGraphCoveredRawTransport.ordered_raw (f.app a)
    (firstCoordinate (π.app a)) (θ.app a)
    (firstCoordinate (π'.app a)) (θ'.app a) (η.app a) ((c'.app a).map ≫ Q.map)
    hn hθ (hr a)
  have hc' := congrArg (fun n ↦ n.map ≫ Q.map) (NatTrans.congr_app hc a)
  change ((JTWhiskeredSeamTarget.nativeOf f).app a).map ≫
    (c'.app a).map ≫ Q.map = (c.app a).map ≫ Q.map at hc'
  rw [JTWhiskeredSeamTarget.nativeOf_app] at hc'
  exact h.trans (by
    simpa only [Category.assoc] using congrArg (firstCoordinate (π.app a) ≫ ·) hc')

private theorem detour_degree {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    (S : JTWhiskeredSeamDiagram.SeamFamily (W := W) (x := x) (y := y) P R K) (a : C) :
    ((pr W x y).map ((JTWhiskeredSeamDiagram.detourToTriangle S).app a)).2 = 𝟙 (K.obj a) :=
  congrArg Prod.snd (JTWhiskeredSeamDiagram.detourToTriangle_projection S a)

private theorem long_degree {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    (S : JTWhiskeredSeamDiagram.SeamFamily (W := W) (x := x) (y := y) P R K) (a : C) :
    ((pr W x y).map ((JTWhiskeredSeamDiagram.longToTriangle S).app a)).2 = 𝟙 (K.obj a) :=
  congrArg Prod.snd (JTWhiskeredSeamDiagram.longToTriangle_projection S a)

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

private theorem evaluation_raw {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (θ : Y ⟶ K ⋙ J) (H : RawDiagram Q G t c π θ) (a : C) :
    lift ((productProjection (codes G.labels) t Q.code Q.map c π).app a ≫ fst _ _)
      (θ.app a) ≫ realizedLabel ((codes G.labels).obj a).toSSet W (K.obj a)
        (JTRealizedLabelEndpoints.orderedLabel W x y ((codes G.labels).obj a) (K.obj a)
          (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            (G.labels.obj a))) =
      ((productProjection (codes G.labels) t Q.code Q.map c π).app a ≫ fst _ _) ≫
        (c.app a).map ≫ Q.map := by
  rw [productProjection_app]
  exact H a

private def evaluate {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (θ : Y ⟶ K ⋙ J) (H : RawDiagram Q G t c π θ) :
    BoundaryNecklaceComma.Presentation
      (JTGraphCoveredLabelEvaluation.reduced Q G.labels t c
        (productProjection (codes G.labels) t Q.code Q.map c π)) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  JTGraphCoveredLabelEvaluation.evaluation Q G.labels t c
    (productProjection (codes G.labels) t Q.code Q.map c π) θ
    (evaluation_raw Q G t c π θ H)

private def evaluationLift {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (θ : Y ⟶ K ⋙ J) (H : RawDiagram Q G t c π θ) :
    JTGraphCoveredLabelEvaluation.reduced Q G.labels t c
        (productProjection (codes G.labels) t Q.code Q.map c π) ⟶
      G.labels ⋙ JTTargetCommaPullback.diagram W x y Q :=
  JTDecoratedIntervalCylinder.liftFromProjections Q G.labels
    (JTGraphCoveredLabelEvaluation.reduced Q G.labels t c
      (productProjection (codes G.labels) t Q.code Q.map c π))
    (JTGraphCoveredLabelEvaluation.decorated Q G.labels t c
      (productProjection (codes G.labels) t Q.code Q.map c π) θ)
    (JTGraphCoveredLabelEvaluation.nativeLeg Q G.labels t c
      (productProjection (codes G.labels) t Q.code Q.map c π))
    (JTGraphCoveredLabelEvaluation.raw_square Q G.labels t c
      (productProjection (codes G.labels) t Q.code Q.map c π) θ
      (evaluation_raw Q G t c π θ H))

private theorem evaluate_eq_mapPresentation {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (θ : Y ⟶ K ⋙ J) (H : RawDiagram Q G t c π θ) :
    evaluate Q G t c π θ H =
      JTBoundaryNecklacePresentationCone.mapPresentation
        (JTTargetCommaPullback.diagram W x y Q)
        (JTGraphCoveredLabelEvaluation.reduced Q G.labels t c
          (productProjection (codes G.labels) t Q.code Q.map c π)) G.labels
        (evaluationLift Q G t c π θ H) ⋙ JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  rfl

private theorem cover_weak {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t)
    (H : ∀ a : C, trivialFibrations SSet.{0} (π.app a)) :
    WeakEquivalence (nerveMap (JTWhiskeredGraphEvaluation.toOriginal Q G t c
      (productProjection (codes G.labels) t Q.code Q.map c π))) := by
  apply JTWhiskeredGraphEvaluation.toOriginal_weak Q G t c
    (productProjection (codes G.labels) t Q.code Q.map c π)
  intro a
  rw [productProjection_app (codes G.labels) t Q.code Q.map c π a]
  exact H a

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- All actual final triangle-filler choices, with the complete original coefficient chain. -/
abbrev Index := JTSharedInsertionNormalizedSeam.Index F j

private abbrev seam := JTSharedInsertionNormalizedSeam.seamFamily F j
private abbrev triangle := (seam F j).triangle
private abbrev detour := JTWhiskeredSeamDiagram.detourFamily (seam F j)
private abbrev long := JTWhiskeredSeamDiagram.longFamily (seam F j)
private abbrev t := JTSharedInsertionPhaseGraph.oldTime F j
private abbrev u := JTSharedInsertionPhaseGraph.triangleToCollapsed F j
private abbrev d := JTSharedInsertionPhaseGraph.detourToCollapsed F j
private abbrev l := JTSharedInsertionPhaseGraph.longToCollapsedNative F j

private theorem checked_triangle_raw :
    RawDiagram Q (triangle F j) (t F j) (JTSharedInsertionSeamNative.triangleTarget F j)
      (JTSharedInsertionSeamGraph.projection F j) (JTSharedInsertionSeamGraph.parameter F j) := by
  intro p
  exact JTSharedInsertionSeamRaw.ordered_raw F j p

/-- The actual common triangle graph has its exact ordered raw value in ORIGINAL Q. -/
theorem triangle_ordered_raw :
    RawDiagram Q (triangle F j) (t F j) (JTSharedInsertionSeamNative.triangleTarget F j)
      (JTSharedInsertionPhaseGraph.projection F j (u F j))
      (JTSharedInsertionPhaseGraph.parameter F j (u F j)) :=
  pull_domain Q (triangle F j) (t F j) (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (JTSharedInsertionSeamGraph.projection F j)
    (JTSharedInsertionPhaseGraph.parameter F j (u F j))
    (JTSharedInsertionSeamGraph.parameter F j)
    (JTSharedInsertionTriangleGraphBridge.iso F j).hom
    (JTSharedInsertionTriangleGraphBridge.iso_projection F j)
    (JTSharedInsertionTriangleGraphBridge.iso_parameter F j) (checked_triangle_raw F j)

/-- The full actual detour graph pulls the same ORIGINAL-Q raw value back through its spine. -/
theorem detour_ordered_raw :
    RawDiagram Q (detour F j) (t F j) (JTSharedInsertionSeamNative.detourTarget F j)
      (JTSharedInsertionPhaseGraph.projection F j (d F j))
      (JTSharedInsertionPhaseGraph.parameter F j (d F j)) := by
  apply pull_arrow Q (detour F j) (triangle F j) (t F j)
    (JTSharedInsertionSeamNative.detourTarget F j) (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (JTSharedInsertionPhaseGraph.parameter F j (d F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j))
    (JTSharedInsertionNormalizedSeam.detourToTriangle F j)
    (JTSharedInsertionPhaseGraph.detourToTriangle F j)
  · exact JTSharedInsertionPhaseGraph.map_projection F j (d F j) (u F j)
      (JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.detourToTriangle F j)) rfl
  · exact JTSharedInsertionPhaseGraph.map_parameter F j (d F j) (u F j)
      (JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.detourToTriangle F j)) rfl
  · exact detour_degree (seam F j)
  · exact JTSharedInsertionSeamNative.detour_target_square F j
  · exact triangle_ordered_raw F j

/-- The full actual long-edge graph retains its exact raw value in that SAME ORIGINAL Q. -/
theorem long_ordered_raw :
    RawDiagram Q (long F j) (t F j) (JTSharedInsertionSeamNative.longTarget F j)
      (JTSharedInsertionPhaseGraph.projection F j (l F j))
      (JTSharedInsertionPhaseGraph.parameter F j (l F j)) := by
  apply pull_arrow Q (long F j) (triangle F j) (t F j)
    (JTSharedInsertionSeamNative.longTarget F j) (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (JTSharedInsertionPhaseGraph.parameter F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j))
    (JTSharedInsertionNormalizedSeam.longToTriangle F j)
    (JTSharedInsertionPhaseGraph.longToTriangle F j)
  · exact JTSharedInsertionPhaseGraph.map_projection F j (l F j) (u F j)
      (JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.longToTriangle F j))
      (JTWhiskeredSeamTarget.long_triangle_collapsed (seam F j))
  · exact JTSharedInsertionPhaseGraph.map_parameter F j (l F j) (u F j)
      (JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.longToTriangle F j))
      (JTWhiskeredSeamTarget.long_triangle_collapsed (seam F j))
  · exact long_degree (seam F j)
  · exact JTSharedInsertionSeamNative.long_target_square F j
  · exact triangle_ordered_raw F j

/-- The complete triangle graph projected to its SAME-Q product with full original time. -/
def triangleProjection : JTSharedInsertionPhaseGraph.triangleGraph F j ⟶
    JTWhiskeredGraphEvaluation.productDiagram Q (triangle F j) (t F j)
      (JTSharedInsertionSeamNative.triangleTarget F j) :=
  productProjection (codes (triangle F j).labels) (t F j) Q.code Q.map
    (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (u F j))

/-- Collapse BOTH full endpoint inverse images of the actual triangle graph. -/
abbrev triangleReduced := JTGraphCoveredLabelEvaluation.reduced Q (triangle F j).labels (t F j)
  (JTSharedInsertionSeamNative.triangleTarget F j) (triangleProjection F j)

/-- The whole actual triangle graph lifts to the original fixed-Q pullback diagram. -/
abbrev trianglePullbackLift := evaluationLift Q (triangle F j) (t F j)
  (JTSharedInsertionSeamNative.triangleTarget F j)
  (JTSharedInsertionPhaseGraph.projection F j (u F j))
  (JTSharedInsertionPhaseGraph.parameter F j (u F j)) (triangle_ordered_raw F j)

/-- Evaluate ALL internal necklaces of the complete triangle graph in ORIGINAL Q. -/
def triangleEvaluation : BoundaryNecklaceComma.Presentation (triangleReduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  evaluate Q (triangle F j) (t F j) (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j)) (triangle_ordered_raw F j)

/-- The full triangle evaluation is exactly the existing map of pullback presentations. -/
theorem triangle_evaluation_eq_mapPresentation : triangleEvaluation F j =
    JTBoundaryNecklacePresentationCone.mapPresentation (JTTargetCommaPullback.diagram W x y Q)
      (triangleReduced F j) (triangle F j).labels (trianglePullbackLift F j) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  evaluate_eq_mapPresentation Q (triangle F j) (t F j)
    (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j)) (triangle_ordered_raw F j)

/-- Forget the complete triangle presentation to its actual final phase-choice index. -/
abbrev triangleToChoices : BoundaryNecklaceComma.Presentation (triangleReduced F j) ⥤ Index F j :=
  JTWhiskeredGraphEvaluation.toOriginal Q (triangle F j) (t F j)
    (JTSharedInsertionSeamNative.triangleTarget F j) (triangleProjection F j)

/-- This whole triangle presentation is a weak cover of NormalizedSeam.Index only. -/
theorem triangleToChoices_weak : WeakEquivalence (nerveMap (triangleToChoices F j)) :=
  cover_weak Q (triangle F j) (t F j) (JTSharedInsertionSeamNative.triangleTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (JTSharedInsertionPhaseGraph.projection_trivialFibration F j (u F j))

/-- The complete detour graph projected to its SAME-Q product with full original time. -/
def detourProjection : JTSharedInsertionPhaseGraph.detourGraph F j ⟶
    JTWhiskeredGraphEvaluation.productDiagram Q (detour F j) (t F j)
      (JTSharedInsertionSeamNative.detourTarget F j) :=
  productProjection (codes (detour F j).labels) (t F j) Q.code Q.map
    (JTSharedInsertionSeamNative.detourTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))

/-- Collapse BOTH full endpoint inverse images of the actual detour graph. -/
abbrev detourReduced := JTGraphCoveredLabelEvaluation.reduced Q (detour F j).labels (t F j)
  (JTSharedInsertionSeamNative.detourTarget F j) (detourProjection F j)

/-- The whole actual detour graph lifts to the original fixed-Q pullback diagram. -/
abbrev detourPullbackLift := evaluationLift Q (detour F j) (t F j)
  (JTSharedInsertionSeamNative.detourTarget F j)
  (JTSharedInsertionPhaseGraph.projection F j (d F j))
  (JTSharedInsertionPhaseGraph.parameter F j (d F j)) (detour_ordered_raw F j)

/-- Evaluate ALL internal necklaces of the complete detour graph in ORIGINAL Q. -/
def detourEvaluation : BoundaryNecklaceComma.Presentation (detourReduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  evaluate Q (detour F j) (t F j) (JTSharedInsertionSeamNative.detourTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.parameter F j (d F j)) (detour_ordered_raw F j)

/-- The full detour evaluation is exactly the existing map of pullback presentations. -/
theorem detour_evaluation_eq_mapPresentation : detourEvaluation F j =
    JTBoundaryNecklacePresentationCone.mapPresentation (JTTargetCommaPullback.diagram W x y Q)
      (detourReduced F j) (detour F j).labels (detourPullbackLift F j) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  evaluate_eq_mapPresentation Q (detour F j) (t F j)
    (JTSharedInsertionSeamNative.detourTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.parameter F j (d F j)) (detour_ordered_raw F j)

/-- Forget the complete detour presentation to its actual final phase-choice index. -/
abbrev detourToChoices : BoundaryNecklaceComma.Presentation (detourReduced F j) ⥤ Index F j :=
  JTWhiskeredGraphEvaluation.toOriginal Q (detour F j) (t F j)
    (JTSharedInsertionSeamNative.detourTarget F j) (detourProjection F j)

/-- This whole detour presentation is a weak cover of NormalizedSeam.Index only. -/
theorem detourToChoices_weak : WeakEquivalence (nerveMap (detourToChoices F j)) :=
  cover_weak Q (detour F j) (t F j) (JTSharedInsertionSeamNative.detourTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.projection_trivialFibration F j (d F j))

/-- The complete long graph projected to its SAME-Q product with full original time. -/
def longProjection : JTSharedInsertionPhaseGraph.longGraph F j ⟶
    JTWhiskeredGraphEvaluation.productDiagram Q (long F j) (t F j)
      (JTSharedInsertionSeamNative.longTarget F j) :=
  productProjection (codes (long F j).labels) (t F j) Q.code Q.map
    (JTSharedInsertionSeamNative.longTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))

/-- Collapse BOTH full endpoint inverse images of the actual long graph. -/
abbrev longReduced := JTGraphCoveredLabelEvaluation.reduced Q (long F j).labels (t F j)
  (JTSharedInsertionSeamNative.longTarget F j) (longProjection F j)

/-- The whole actual long graph lifts to the original fixed-Q pullback diagram. -/
abbrev longPullbackLift := evaluationLift Q (long F j) (t F j)
  (JTSharedInsertionSeamNative.longTarget F j)
  (JTSharedInsertionPhaseGraph.projection F j (l F j))
  (JTSharedInsertionPhaseGraph.parameter F j (l F j)) (long_ordered_raw F j)

/-- Evaluate ALL internal necklaces of the complete long graph in ORIGINAL Q. -/
def longEvaluation : BoundaryNecklaceComma.Presentation (longReduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  evaluate Q (long F j) (t F j) (JTSharedInsertionSeamNative.longTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (l F j)) (long_ordered_raw F j)

/-- The full long evaluation is exactly the existing map of pullback presentations. -/
theorem long_evaluation_eq_mapPresentation : longEvaluation F j =
    JTBoundaryNecklacePresentationCone.mapPresentation (JTTargetCommaPullback.diagram W x y Q)
      (longReduced F j) (long F j).labels (longPullbackLift F j) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  evaluate_eq_mapPresentation Q (long F j) (t F j)
    (JTSharedInsertionSeamNative.longTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (l F j)) (long_ordered_raw F j)

/-- Forget the complete long presentation to its actual final phase-choice index. -/
abbrev longToChoices : BoundaryNecklaceComma.Presentation (longReduced F j) ⥤ Index F j :=
  JTWhiskeredGraphEvaluation.toOriginal Q (long F j) (t F j)
    (JTSharedInsertionSeamNative.longTarget F j) (longProjection F j)

/-- This whole long presentation is a weak cover of NormalizedSeam.Index only. -/
theorem longToChoices_weak : WeakEquivalence (nerveMap (longToChoices F j)) :=
  cover_weak Q (long F j) (t F j) (JTSharedInsertionSeamNative.longTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection_trivialFibration F j (l F j))

end
end DaggerModels.PartII.JTSharedInsertionPhaseRaw
