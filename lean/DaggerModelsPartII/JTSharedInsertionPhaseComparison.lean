import DaggerModelsPartII.JTSharedInsertionPhaseRaw
import DaggerModelsPartII.JTSharedInsertionOldComparison
import DaggerModelsPartII.JTGraphCoveredLiftComparison
import DaggerModelsPartII.JTReindexedEndpointCoverTransport

/-!
# Actual full detour and long comparisons in the original Q

Both phase graph maps preserve the whole original-time product and lifted
coefficient parameter. Transport the complete inverse images of BOTH endpoint
lines, descend their full reduced source maps, and use the existing fixed-Q
pullback comparison on every internal necklace. All actual inputs are derived
from F and j; no caller source-change, raw, support or compatibility premise is
added. The identity-edge collapse uses the already checked collapsed raw value
and evaluation, retaining the same original Q and full old time.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionPhaseComparison

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def retarget {C : Type} [SmallCategory C] {X X' Y Y' : C ⥤ SSet.{0}}
    (e : X ≅ X') (f : Y ≅ Y') (n : X ⟶ Y) : X' ⟶ Y' := e.inv ≫ n ≫ f.hom

private theorem retarget_square {C : Type} [SmallCategory C]
    {X X' Y Y' NY MY : C ⥤ SSet.{0}}
    (e : X ≅ X') (f : Y ≅ Y') (n : X ⟶ Y)
    (np : NY ⟶ X) (mp : MY ⟶ Y) (η : NY ⟶ MY) (hp : η ≫ mp = np ≫ n) :
    η ≫ (mp ≫ f.hom) = (np ≫ e.hom) ≫ retarget e f n := by
  rw [← Category.assoc, hp]
  simp only [retarget, Category.assoc, Iso.hom_inv_id_assoc]

private theorem product_iso_inv_app {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) (U : NecklaceCode)
    {X : SSet.{0}} (q : U.toSSet ⟶ X) (c : N ⟶ (Functor.const C).obj U) (a : C) :
    (JTGraphCoveredProductInterface.iso N t U q c).inv.app a = 𝟙 _ := rfl

private theorem timeMap_app {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (n : N ⟶ M) (t : C ⥤ SimplexCategory) (a : C) :
    (JTSharedInsertionPhaseGraph.mapWithTime n t).app a =
      (n.app a).map ⊗ₘ 𝟙 (J.obj (t.obj a)) := rfl

private theorem endpoint_tensor {N M : NecklaceCode} (n : N ⟶ M) (t : SimplexCategory) :
    (JTNecklaceEndpointCylinder.endpointInclusion N ⊗ₘ 𝟙 (J.obj t)) ≫
        (n.map ⊗ₘ 𝟙 (J.obj t)) =
      JTNecklaceEndpointCylinder.endpointInclusion M ⊗ₘ 𝟙 (J.obj t) := by
  rw [tensorHom_comp_tensorHom, Category.id_comp,
    JTNecklaceEndpointCylinder.endpointInclusion_natural]

section Transport

variable {C : Type} [SmallCategory C] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (N M : C ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : C ⥤ SimplexCategory)
variable (nc : codes N ⟶ (Functor.const C).obj Q.code)
variable (mc : codes M ⟶ (Functor.const C).obj Q.code)
variable {NY MY : C ⥤ SSet.{0}}
variable (np : NY ⟶ JTGraphCoveredProductInterface.product (codes N) t)
variable (mp : MY ⟶ JTGraphCoveredProductInterface.product (codes M) t)
variable (r : N ⟶ M) (η : NY ⟶ MY)
variable (hp : η ≫ mp = np ≫
  JTSharedInsertionPhaseGraph.mapWithTime (JTWhiskeredSeamTarget.nativeOf r) t)

private abbrev newIso := JTGraphCoveredProductInterface.iso (codes N) t Q.code Q.map nc
private abbrev oldIso := JTGraphCoveredProductInterface.iso (codes M) t Q.code Q.map mc
private def newProjection := np ≫ (newIso Q N t nc).hom
private def oldProjection := mp ≫ (oldIso Q M t mc).hom
private def productChange := retarget (newIso Q N t nc) (oldIso Q M t mc)
  (JTSharedInsertionPhaseGraph.mapWithTime (JTWhiskeredSeamTarget.nativeOf r) t)

include hp in
private theorem projection_square : η ≫ oldProjection Q M t mc mp =
    newProjection Q N t nc np ≫ productChange Q N M t nc mc r :=
  retarget_square (newIso Q N t nc) (oldIso Q M t mc)
    (JTSharedInsertionPhaseGraph.mapWithTime (JTWhiskeredSeamTarget.nativeOf r) t)
    np mp η hp

private theorem productChange_app (a : C) :
    ((productChange Q N M t nc mc r).app a :
      ((codes N).obj a).toSSet ⊗ J.obj (t.obj a) ⟶
        ((codes M).obj a).toSSet ⊗ J.obj (t.obj a)) =
      ((JTWhiskeredSeamTarget.nativeOf r).app a).map ⊗ₘ 𝟙 (J.obj (t.obj a)) := by
  simp only [productChange, retarget, NatTrans.comp_app, product_iso_inv_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.id_comp, Category.comp_id,
    timeMap_app]

private abbrev newBoundary := JTGraphCoveredLabelEvaluation.boundary Q N t nc
private abbrev oldBoundary := JTGraphCoveredLabelEvaluation.boundary Q M t mc
private abbrev endpoint := Functor.whiskerLeft t JTXiEndpointCollapse.cylinderProjection
private abbrev endpointDomain := t ⋙ JTXiEndpointCollapse.boundaryCylinder

private theorem boundary_square : newBoundary Q N t nc ≫ productChange Q N M t nc mc r =
    (𝟙 (endpointDomain t)) ≫ Functor.whiskerLeft (𝟭 C) (oldBoundary Q M t mc) := by
  apply NatTrans.ext
  funext a
  change (JTNecklaceEndpointCylinder.endpointInclusion ((codes N).obj a) ⊗ₘ 𝟙 _) ≫
      (productChange Q N M t nc mc r).app a =
    𝟙 _ ≫ (JTNecklaceEndpointCylinder.endpointInclusion ((codes M).obj a) ⊗ₘ 𝟙 _)
  rw [productChange_app, Category.id_comp]
  exact endpoint_tensor ((JTWhiskeredSeamTarget.nativeOf r).app a) (t.obj a)

private abbrev newReduced := JTGraphCoveredLabelEvaluation.reduced Q N t nc
  (newProjection Q N t nc np)
private abbrev oldReduced := JTGraphCoveredLabelEvaluation.reduced Q M t mc
  (oldProjection Q M t mc mp)

include r η hp in
private def fullSourceChange : newReduced Q N t nc np ⟶ oldReduced Q M t mc mp :=
  JTReindexedEndpointCoverTransport.sourceChange (𝟭 C)
    (oldProjection Q M t mc mp) (oldBoundary Q M t mc) (endpoint t)
    (newProjection Q N t nc np) (newBoundary Q N t nc) (endpoint t)
    (productChange Q N M t nc mc r) η (𝟙 (endpointDomain t))
    (projection_square Q N M t nc mc np mp r η hp)
    (boundary_square Q N M t nc mc r) (fun _ ↦ Category.id_comp _)

include r η hp in
private theorem fullSourceChange_cylinder (a : C) :
    (JTGraphCoveredCylinderEquations.inc Q N t nc (newProjection Q N t nc np)).app a ≫
        ((fullSourceChange Q N M t nc mc np mp r η hp).app a).right =
      η.app a ≫ (JTGraphCoveredCylinderEquations.inc Q M t mc
        (oldProjection Q M t mc mp)).app a :=
  JTReindexedEndpointCoverTransport.sourceChange_cylinder (𝟭 C)
    (oldProjection Q M t mc mp) (oldBoundary Q M t mc) (endpoint t)
    (newProjection Q N t nc np) (newBoundary Q N t nc) (endpoint t)
    (productChange Q N M t nc mc r) η (𝟙 (endpointDomain t))
    (projection_square Q N M t nc mc np mp r η hp)
    (boundary_square Q N M t nc mc r) (fun _ ↦ Category.id_comp _) a

include hp in
private theorem native_coordinate (a : C) :
    ((newProjection Q N t nc np).app a ≫
      fst ((codes N).obj a).toSSet (J.obj (t.obj a))) ≫
        ((JTGraphCoveredEvaluationSquares.nativePart (N := N) (M := M) (𝟭 C) r).app a).map =
      η.app a ≫ (oldProjection Q M t mc mp).app a ≫
        fst ((codes M).obj a).toSSet (J.obj (t.obj a)) := by
  have h := congrArg (fun f ↦ f ≫ fst ((codes M).obj a).toSSet (J.obj (t.obj a)))
    (NatTrans.congr_app (projection_square Q N M t nc mc np mp r η hp) a)
  simpa only [NatTrans.comp_app, productChange_app, Category.assoc, tensorHom_fst] using h.symm

variable (nq : NY ⟶ JTParametrizedTargetFamilyComparison.degrees N ⋙ J)
variable (mq : MY ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
variable (hq : ∀ a, nq.app a ≫
  J.map ((JTGraphCoveredEvaluationSquares.degreePart (N := N) (M := M) (𝟭 C) r).app a) =
    η.app a ≫ mq.app a)
variable (hc : JTGraphCoveredEvaluationSquares.nativePart (N := N) (M := M) (𝟭 C) r ≫
  Functor.whiskerLeft (𝟭 C) mc = nc)
variable (nr : JTGraphCoveredLiftComparison.RawEquation Q N t nc
  (newProjection Q N t nc np) nq)
variable (mr : JTGraphCoveredLiftComparison.RawEquation Q M t mc
  (oldProjection Q M t mc mp) mq)

include r η hp in
private def fullPresentation : BoundaryNecklaceComma.Presentation (newReduced Q N t nc np) ⥤
    BoundaryNecklaceComma.Presentation (oldReduced Q M t mc mp) :=
  JTGraphCoveredLiftComparison.presentationMap Q (𝟭 C) N M t t nc mc
    (newProjection Q N t nc np) (oldProjection Q M t mc mp)
    (fullSourceChange Q N M t nc mc np mp r η hp)

include hp hq hc in
private def fullComparison :
    JTGraphCoveredLabelEvaluation.evaluation Q N t nc
        (newProjection Q N t nc np) nq nr ⟶
      fullPresentation Q N M t nc mc np mp r η hp ⋙
        JTGraphCoveredLabelEvaluation.evaluation Q M t mc
          (oldProjection Q M t mc mp) mq mr :=
  JTGraphCoveredLiftComparison.comparison Q (𝟭 C) N M t t nc mc
    (newProjection Q N t nc np) (oldProjection Q M t mc mp) nq mq r η
    (fullSourceChange Q N M t nc mc np mp r η hp)
    (fullSourceChange_cylinder Q N M t nc mc np mp r η hp)
    (native_coordinate Q N M t nc mc np mp r η hp) hq hc nr mr


end Transport

private theorem product_projection_app {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) (U : NecklaceCode)
    {X : SSet.{0}} (q : U.toSSet ⟶ X) (c : N ⟶ (Functor.const C).obj U)
    {Y : C ⥤ SSet.{0}} (π : Y ⟶ JTGraphCoveredProductInterface.product N t) (a : C) :
    ((π ≫ (JTGraphCoveredProductInterface.iso N t U q c).hom).app a :
      Y.obj a ⟶ (N.obj a).toSSet ⊗ J.obj (t.obj a)) = π.app a := by
  simp only [NatTrans.comp_app, JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id]

-- Match the checked phase-raw certificate view before specializing the actual Family.
private def firstCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ fst B T

private def familyRawAt {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (a : C) {X : SSet.{0}} (h : X ⟶ ((codes G.labels).obj a).toSSet)
    (q : X ⟶ J.obj (K.obj a)) (g : ((codes G.labels).obj a).toSSet ⟶ Raw W) : Prop :=
  lift h q ≫ JTNecklaceLabelRealization.realizedLabel ((codes G.labels).obj a).toSSet W
      (K.obj a) (JTRealizedLabelEndpoints.orderedLabel W x y ((codes G.labels).obj a)
        (K.obj a) (OrderedLabelElements.label W
          (OrderedNecklaceVertexPoints.boundaryPoint W x y) (G.labels.obj a))) = h ≫ g

private def familyRawDiagram {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t) (θ : Y ⟶ K ⋙ J) :
    Prop := ∀ a, familyRawAt G a (firstCoordinate (π.app a)) (θ.app a)
      ((c.app a).map ≫ Q.map)

private theorem family_rawEquation {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t) (θ : Y ⟶ K ⋙ J)
    (H : familyRawDiagram Q G t c π θ) :
    JTGraphCoveredLiftComparison.RawEquation Q G.labels t c
      (π ≫ (JTGraphCoveredProductInterface.iso (codes G.labels) t Q.code Q.map c).hom) θ := by
  intro a
  rw [product_projection_app]
  exact H a

-- The collapsed raw API is expressed directly in the decorated label degree.
private def labelRawAt {C : Type} [SmallCategory C] {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (N : C ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : C ⥤ SimplexCategory)
    (c : codes N ⟶ (Functor.const C).obj Q.code) {X : C ⥤ SSet.{0}}
    (π : X ⟶ JTGraphCoveredProductInterface.product (codes N) t)
    (θ : X ⟶ JTParametrizedTargetFamilyComparison.degrees N ⋙ J) (a : C) : Prop :=
  lift (π.app a ≫ fst ((codes N).obj a).toSSet (J.obj (t.obj a))) (θ.app a) ≫
    JTNecklaceLabelRealization.realizedLabel ((codes N).obj a).toSSet W
      ((JTParametrizedTargetFamilyComparison.degrees N).obj a)
      (JTRealizedLabelEndpoints.orderedLabel W x y ((codes N).obj a)
        ((JTParametrizedTargetFamilyComparison.degrees N).obj a)
        (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
          (N.obj a))) =
    (π.app a ≫ fst ((codes N).obj a).toSSet (J.obj (t.obj a))) ≫ (c.app a).map ≫ Q.map

private theorem family_rawEquation_from_labels {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTGraphCoveredProductInterface.product (codes G.labels) t) (θ : Y ⟶ K ⋙ J)
    (H : ∀ a, labelRawAt Q G.labels t c π θ a) :
    JTGraphCoveredLiftComparison.RawEquation Q G.labels t c
      (π ≫ (JTGraphCoveredProductInterface.iso (codes G.labels) t Q.code Q.map c).hom) θ := by
  intro a
  rw [product_projection_app]
  exact H a

private theorem trace_coordinate {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R P' R' : C ⥤ NecklaceCode}
    {K : C ⥤ SimplexCategory} {M N : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (H : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) N P' R' K)
    {X Y : C ⥤ SSet.{0}} (nq : X ⟶ K ⋙ J) (mq : Y ⟶ K ⋙ J)
    (r : G.labels ⟶ H.labels) (η : X ⟶ Y) (hθ : η ≫ mq = nq)
    (hd : ∀ a, ((OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map (r.app a)).2 = 𝟙 (K.obj a)) (a : C) :
    nq.app a ≫ J.map ((JTGraphCoveredEvaluationSquares.degreePart
      (N := G.labels) (M := H.labels) (𝟭 C) r).app a) =
      η.app a ≫ mq.app a := by
  have h : (JTGraphCoveredEvaluationSquares.degreePart
      (N := G.labels) (M := H.labels) (𝟭 C) r).app a = 𝟙 (K.obj a) := hd a
  rw [h, J.map_id]
  change nq.app a = η.app a ≫ mq.app a
  exact (NatTrans.congr_app hθ a).symm

private theorem detour_degree {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    (S : JTWhiskeredSeamDiagram.SeamFamily (W := W) (x := x) (y := y) P R K) (a : C) :
    ((OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      ((JTWhiskeredSeamDiagram.detourToTriangle S).app a)).2 = 𝟙 (K.obj a) :=
  congrArg Prod.snd (JTWhiskeredSeamDiagram.detourToTriangle_projection S a)

private theorem long_degree {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    (S : JTWhiskeredSeamDiagram.SeamFamily (W := W) (x := x) (y := y) P R K) (a : C) :
    ((OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      ((JTWhiskeredSeamDiagram.longToTriangle S).app a)).2 = 𝟙 (K.obj a) :=
  congrArg Prod.snd (JTWhiskeredSeamDiagram.longToTriangle_projection S a)

private theorem collapsed_degree {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    (S : JTWhiskeredSeamDiagram.SeamFamily (W := W) (x := x) (y := y) P R K) (a : C) :
    ((OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      ((JTWhiskeredSeamDiagram.longToCollapsed S).app a)).2 = 𝟙 (K.obj a) :=
  congrArg Prod.snd (JTWhiskeredSeamDiagram.longToCollapsed_projection S a)

private theorem target_identity {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W}
    {N M : C ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ M)
    {U : NecklaceCode} (nc : codes N ⟶ (Functor.const C).obj U)
    (mc : codes M ⟶ (Functor.const C).obj U)
    (h : JTWhiskeredSeamTarget.nativeOf r ≫ mc = nc) :
    JTGraphCoveredEvaluationSquares.nativePart (N := N) (M := M) (𝟭 C) r ≫
      Functor.whiskerLeft (𝟭 C) mc = nc := h

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev I := JTSharedInsertionNormalizedSeam.Index F j
private abbrev seam := JTSharedInsertionNormalizedSeam.seamFamily F j
private abbrev P := JTSharedInsertionSeamTriangles.toOriginal F j ⋙
  JTSharedInsertionSeamSurroundings.leftNative F j
private abbrev R := JTSharedInsertionSeamTriangles.toOriginal F j ⋙
  JTSharedInsertionSeamSurroundings.rightNative F j
private abbrev K := JTSharedInsertionSeamTriangles.ordinals F j
private abbrev triangle := (seam F j).triangle
private abbrev detour := JTWhiskeredSeamDiagram.detourFamily (seam F j)
private abbrev long := JTWhiskeredSeamDiagram.longFamily (seam F j)
private abbrev t := JTSharedInsertionPhaseGraph.oldTime F j
private abbrev triTarget := JTSharedInsertionSeamNative.triangleTarget F j
private abbrev detTarget := JTSharedInsertionSeamNative.detourTarget F j
private abbrev longTarget := JTSharedInsertionSeamNative.longTarget F j
private abbrev u := JTSharedInsertionPhaseGraph.triangleToCollapsed F j
private abbrev d := JTSharedInsertionPhaseGraph.detourToCollapsed F j
private abbrev l := JTSharedInsertionPhaseGraph.longToCollapsedNative F j
private abbrev detArrow := JTSharedInsertionNormalizedSeam.detourToTriangle F j
private abbrev longArrow := JTSharedInsertionNormalizedSeam.longToTriangle F j
private abbrev detMap := JTSharedInsertionPhaseGraph.detourToTriangle F j
private abbrev longMap := JTSharedInsertionPhaseGraph.longToTriangle F j

private theorem detProjection : detMap F j ≫
    JTSharedInsertionPhaseGraph.projection F j (u F j) =
      JTSharedInsertionPhaseGraph.projection F j (d F j) ≫
        JTSharedInsertionPhaseGraph.mapWithTime
          (JTWhiskeredSeamTarget.nativeOf (detArrow F j)) (t F j) :=
  JTSharedInsertionPhaseGraph.map_projection F j (d F j) (u F j)
    (JTWhiskeredSeamTarget.nativeOf (detArrow F j)) rfl

private theorem longProjection : longMap F j ≫
    JTSharedInsertionPhaseGraph.projection F j (u F j) =
      JTSharedInsertionPhaseGraph.projection F j (l F j) ≫
        JTSharedInsertionPhaseGraph.mapWithTime
          (JTWhiskeredSeamTarget.nativeOf (longArrow F j)) (t F j) :=
  JTSharedInsertionPhaseGraph.map_projection F j (l F j) (u F j)
    (JTWhiskeredSeamTarget.nativeOf (longArrow F j))
    (JTWhiskeredSeamTarget.long_triangle_collapsed (seam F j))

/-- The WHOLE reduced detour source maps naturally to the WHOLE triangle source. -/
def detourSourceChange : JTSharedInsertionPhaseRaw.detourReduced F j ⟶
    JTSharedInsertionPhaseRaw.triangleReduced F j :=
  fullSourceChange Q (detour F j).labels (triangle F j).labels (t F j)
    (detTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (detArrow F j) (detMap F j) (detProjection F j)

/-- The WHOLE reduced identity-edge source maps to that SAME full triangle source. -/
def longSourceChange : JTSharedInsertionPhaseRaw.longReduced F j ⟶
    JTSharedInsertionPhaseRaw.triangleReduced F j :=
  fullSourceChange Q (long F j).labels (triangle F j).labels (t F j)
    (longTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (longArrow F j) (longMap F j) (longProjection F j)

/-- The detour source change preserves the ENTIRE graph-domain summand. -/
theorem detour_sourceChange_cylinder (p : I F j) :
    (JTGraphCoveredCylinderEquations.inc Q (detour F j).labels (t F j) (detTarget F j)
      (JTSharedInsertionPhaseRaw.detourProjection F j)).app p ≫
        ((detourSourceChange F j).app p).right =
      (detMap F j).app p ≫ (JTGraphCoveredCylinderEquations.inc Q (triangle F j).labels
        (t F j) (triTarget F j) (JTSharedInsertionPhaseRaw.triangleProjection F j)).app p :=
  fullSourceChange_cylinder Q (detour F j).labels (triangle F j).labels (t F j)
    (detTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (detArrow F j) (detMap F j) (detProjection F j) p

/-- The long source change likewise preserves ALL graph points, not only vertices. -/
theorem long_sourceChange_cylinder (p : I F j) :
    (JTGraphCoveredCylinderEquations.inc Q (long F j).labels (t F j) (longTarget F j)
      (JTSharedInsertionPhaseRaw.longProjection F j)).app p ≫
        ((longSourceChange F j).app p).right =
      (longMap F j).app p ≫ (JTGraphCoveredCylinderEquations.inc Q (triangle F j).labels
        (t F j) (triTarget F j) (JTSharedInsertionPhaseRaw.triangleProjection F j)).app p :=
  fullSourceChange_cylinder Q (long F j).labels (triangle F j).labels (t F j)
    (longTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (longArrow F j) (longMap F j) (longProjection F j) p

private def triangleRaw :=
  family_rawEquation (P := P F j) (R := R F j) (K := K F j)
    (M := single 2) Q (triangle F j) (t F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j))
    (JTSharedInsertionPhaseRaw.triangle_ordered_raw F j)

private def detourRaw :=
  family_rawEquation (P := P F j) (R := R F j) (K := K F j)
    (M := wedge (single 1) (single 1)) Q (detour F j) (t F j) (detTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.parameter F j (d F j))
    (JTSharedInsertionPhaseRaw.detour_ordered_raw F j)

private def detourTrace (p : I F j) :=
  trace_coordinate (P := P F j) (R := R F j) (P' := P F j) (R' := R F j)
    (K := K F j) (M := wedge (single 1) (single 1)) (N := single 2) (detour F j) (triangle F j)
    (JTSharedInsertionPhaseGraph.parameter F j (d F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j)) (detArrow F j) (detMap F j)
    (JTSharedInsertionPhaseGraph.map_parameter F j (d F j) (u F j)
      (JTWhiskeredSeamTarget.nativeOf (detArrow F j)) rfl) (detour_degree (seam F j)) p

private def detourTargetSquare :=
  target_identity (detArrow F j) (detTarget F j) (triTarget F j)
    (JTSharedInsertionSeamNative.detour_target_square F j)

/-- Transport ALL internal detour necklaces along the full reduced source change. -/
def detourPresentation :
    BoundaryNecklaceComma.Presentation (JTSharedInsertionPhaseRaw.detourReduced F j) ⥤
      BoundaryNecklaceComma.Presentation (JTSharedInsertionPhaseRaw.triangleReduced F j) :=
  fullPresentation Q (detour F j).labels (triangle F j).labels (t F j)
    (detTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (detArrow F j) (detMap F j) (detProjection F j)

/-- The actual detour-to-triangle evaluation comparison in the SAME original Q. -/
def detourComparison : JTSharedInsertionPhaseRaw.detourEvaluation F j ⟶
    detourPresentation F j ⋙ JTSharedInsertionPhaseRaw.triangleEvaluation F j :=
  fullComparison Q (detour F j).labels (triangle F j).labels (t F j)
    (detTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (d F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (detArrow F j) (detMap F j) (detProjection F j)
    (JTSharedInsertionPhaseGraph.parameter F j (d F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j))
    (detourTrace F j) (detourTargetSquare F j) (detourRaw F j) (triangleRaw F j)

private def longRaw :=
  family_rawEquation (P := P F j) (R := R F j) (K := K F j)
    (M := single 1) Q (long F j) (t F j) (longTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (l F j))
    (JTSharedInsertionPhaseRaw.long_ordered_raw F j)

private def longTrace (p : I F j) :=
  trace_coordinate (P := P F j) (R := R F j) (P' := P F j) (R' := R F j)
    (K := K F j) (M := single 1) (N := single 2) (long F j) (triangle F j)
    (JTSharedInsertionPhaseGraph.parameter F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j)) (longArrow F j) (longMap F j)
    (JTSharedInsertionPhaseGraph.map_parameter F j (l F j) (u F j)
      (JTWhiskeredSeamTarget.nativeOf (longArrow F j))
      (JTWhiskeredSeamTarget.long_triangle_collapsed (seam F j))) (long_degree (seam F j)) p

private def longTargetSquare :=
  target_identity (N := (long F j).labels) (M := (triangle F j).labels)
    (longArrow F j) (longTarget F j) (triTarget F j)
    (JTSharedInsertionSeamNative.long_target_square F j)

/-- Transport ALL internal long necklaces along the full reduced source change. -/
def longPresentation :
    BoundaryNecklaceComma.Presentation (JTSharedInsertionPhaseRaw.longReduced F j) ⥤
      BoundaryNecklaceComma.Presentation (JTSharedInsertionPhaseRaw.triangleReduced F j) :=
  fullPresentation Q (long F j).labels (triangle F j).labels (t F j)
    (longTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (longArrow F j) (longMap F j) (longProjection F j)

/-- The actual long-to-triangle evaluation comparison in the SAME original Q. -/
def longComparison : JTSharedInsertionPhaseRaw.longEvaluation F j ⟶
    longPresentation F j ⋙ JTSharedInsertionPhaseRaw.triangleEvaluation F j :=
  fullComparison Q (long F j).labels (triangle F j).labels (t F j)
    (longTarget F j) (triTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (u F j))
    (longArrow F j) (longMap F j) (longProjection F j)
    (JTSharedInsertionPhaseGraph.parameter F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (u F j))
    (longTrace F j) (longTargetSquare F j) (longRaw F j) (triangleRaw F j)


private abbrev collapsed := JTWhiskeredSeamDiagram.collapsedFamily (seam F j)
private abbrev collapsedTarget := JTSharedInsertionSeamNative.collapsedTarget F j
private abbrev collapseArrow := JTSharedInsertionNormalizedSeam.longToCollapsed F j
private abbrev collapseMap := JTSharedInsertionPhaseGraph.longToCollapsed F j
private abbrev c := 𝟙 (JTSharedInsertionPhaseGraph.collapsedCodes F j)

private theorem collapseProjection : collapseMap F j ≫
    JTSharedInsertionPhaseGraph.projection F j (c F j) =
      JTSharedInsertionPhaseGraph.projection F j (l F j) ≫
        JTSharedInsertionPhaseGraph.mapWithTime
          (JTWhiskeredSeamTarget.nativeOf (collapseArrow F j)) (t F j) :=
  JTSharedInsertionPhaseGraph.map_projection F j (l F j) (c F j)
    (JTWhiskeredSeamTarget.nativeOf (collapseArrow F j)) (Category.comp_id _)

/-- The whole long source maps into the whole collapsed source, with both endpoint fibers. -/
def longToCollapsedSourceChange : JTSharedInsertionPhaseRaw.longReduced F j ⟶
    JTSharedInsertionOldComparison.reduced F j :=
  fullSourceChange Q (long F j).labels (collapsed F j).labels (t F j)
    (longTarget F j) (collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (c F j))
    (collapseArrow F j) (collapseMap F j) (collapseProjection F j)

/-- The identity-edge collapse preserves the ENTIRE graph-domain summand. -/
theorem longToCollapsed_sourceChange_cylinder (p : I F j) :
    (JTGraphCoveredCylinderEquations.inc Q (long F j).labels (t F j) (longTarget F j)
      (JTSharedInsertionPhaseRaw.longProjection F j)).app p ≫
        ((longToCollapsedSourceChange F j).app p).right =
      (collapseMap F j).app p ≫ (JTGraphCoveredCylinderEquations.inc Q (collapsed F j).labels
        (t F j) (collapsedTarget F j)
        (JTSharedInsertionOldComparison.projectionTarget F j)).app p :=
  fullSourceChange_cylinder Q (long F j).labels (collapsed F j).labels (t F j)
    (longTarget F j) (collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (c F j))
    (collapseArrow F j) (collapseMap F j) (collapseProjection F j) p

private def collapsedRaw :=
  family_rawEquation_from_labels (P := P F j) (R := R F j) (K := K F j)
    (M := single 0) Q (collapsed F j) (t F j) (collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (c F j))
    (JTSharedInsertionPhaseGraph.parameter F j (c F j))
    (JTSharedInsertionOldComparison.ordered_raw F j)

private def collapseTrace (p : I F j) :=
  trace_coordinate (P := P F j) (R := R F j) (P' := P F j) (R' := R F j)
    (K := K F j) (M := single 1) (N := single 0) (long F j) (collapsed F j)
    (JTSharedInsertionPhaseGraph.parameter F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (c F j)) (collapseArrow F j) (collapseMap F j)
    (JTSharedInsertionPhaseGraph.map_parameter F j (l F j) (c F j)
      (JTWhiskeredSeamTarget.nativeOf (collapseArrow F j)) (Category.comp_id _))
    (collapsed_degree (P := P F j) (R := R F j) (K := K F j) (seam F j)) p

private def collapseTargetSquare :=
  target_identity (N := (long F j).labels) (M := (collapsed F j).labels)
    (collapseArrow F j) (longTarget F j) (collapsedTarget F j)
    (JTSharedInsertionSeamNative.collapsed_target_square F j)

/-- Transport ALL internal long necklaces through the full identity-edge collapse. -/
def longToCollapsedPresentation :
    BoundaryNecklaceComma.Presentation (JTSharedInsertionPhaseRaw.longReduced F j) ⥤
      BoundaryNecklaceComma.Presentation (JTSharedInsertionOldComparison.reduced F j) :=
  fullPresentation Q (long F j).labels (collapsed F j).labels (t F j)
    (longTarget F j) (collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (c F j))
    (collapseArrow F j) (collapseMap F j) (collapseProjection F j)

/-- The actual long-to-collapsed evaluation comparison in the SAME original Q. -/
def longToCollapsedComparison : JTSharedInsertionPhaseRaw.longEvaluation F j ⟶
    longToCollapsedPresentation F j ⋙ JTSharedInsertionOldComparison.evaluation F j :=
  fullComparison Q (long F j).labels (collapsed F j).labels (t F j)
    (longTarget F j) (collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.projection F j (l F j))
    (JTSharedInsertionPhaseGraph.projection F j (c F j))
    (collapseArrow F j) (collapseMap F j) (collapseProjection F j)
    (JTSharedInsertionPhaseGraph.parameter F j (l F j))
    (JTSharedInsertionPhaseGraph.parameter F j (c F j))
    (collapseTrace F j) (collapseTargetSquare F j) (longRaw F j) (collapsedRaw F j)


end
end DaggerModels.PartII.JTSharedInsertionPhaseComparison
