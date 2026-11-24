import DaggerModelsPartII.JTSharedInsertionCoarseEvaluation
import DaggerModelsPartII.JTSharedInsertionCoarseGraphComparison
import DaggerModelsPartII.JTSharedInsertionCoarseDecoratedComparison
import DaggerModelsPartII.JTSharedInsertionOldRaw
import DaggerModelsPartII.JTGraphCoveredLiftComparison
import DaggerModelsPartII.JTReindexedEndpointCoverTransport

/-!
# Full original-Q evaluation comparison for the actual old and coarse labels

Transport the complete inverse images of both endpoint lines and their reduced
cylinders. Existing graph and decorated comparisons preserve all original time,
coefficient operators and the exact fixed Q. All internal necklaces are kept.
No caller raw equation, compatibility, Family or section is added.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseEvaluationComparison

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (row W ⦋0⦌).obj (op ⦋0⦌)
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

include r η hp in
private theorem fullPresentation_forget :
    fullPresentation Q N M t nc mc np mp r η hp ⋙
        Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (oldReduced Q M t mc mp)) =
      Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (newReduced Q N t nc np)) := by
  change (Grothendieck.map _ ⋙ Grothendieck.pre _ (𝟭 C)) ⋙ Grothendieck.forget _ = _
  rw [Grothendieck.pre_id, Functor.comp_id]
  exact Grothendieck.functor_comp_forget

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

private theorem family_evaluation_eq {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory) (c : codes G.labels ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTWhiskeredGraphEvaluation.productDiagram Q G t c) (θ : Y ⟶ K ⋙ J)
    (H : ∀ a, JTWhiskeredGraphRaw.PieceEquations W (G.data a)
      (JTWhiskeredGraphEvaluation.nativeCoordinate Q G t c π a) (θ.app a)
      (JTWhiskeredGraphEvaluation.rawTarget Q G c a))
    (hr : JTGraphCoveredLiftComparison.RawEquation Q G.labels t c π θ) :
    JTWhiskeredGraphEvaluation.evaluation Q G t c π θ H =
      JTGraphCoveredLabelEvaluation.evaluation Q G.labels t c π θ hr := rfl

private theorem trace_coordinate {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R P' M' R' : C ⥤ NecklaceCode}
    {K : C ⥤ SimplexCategory} {M : NecklaceCode}
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (H : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y) P' M' R' K)
    {X Y : C ⥤ SSet.{0}} (nq : X ⟶ K ⋙ J) (mq : Y ⟶ K ⋙ J)
    (r : G.labels ⟶ H.labels) (η : X ⟶ Y) (hθ : η ≫ mq = nq)
    (hd : JTParametrizedTargetFamilyComparison.coefficient r = 𝟙 K) (a : C) :
    nq.app a ≫ J.map ((JTGraphCoveredEvaluationSquares.degreePart
      (N := G.labels) (M := H.labels) (𝟭 C) r).app a) =
      η.app a ≫ mq.app a := by
  have h : (JTGraphCoveredEvaluationSquares.degreePart
      (N := G.labels) (M := H.labels) (𝟭 C) r).app a = 𝟙 (K.obj a) :=
    NatTrans.congr_app hd a
  rw [h, J.map_id]
  change nq.app a = η.app a ≫ mq.app a
  exact (NatTrans.congr_app hθ a).symm

private theorem target_identity {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W}
    {N M : C ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ M)
    {U : NecklaceCode} (nc : codes N ⟶ (Functor.const C).obj U)
    (mc : codes M ⟶ (Functor.const C).obj U)
    (h : JTWhiskeredSeamTarget.nativeOf r ≫ mc = nc) :
    JTGraphCoveredEvaluationSquares.nativePart (N := N) (M := M) (𝟭 C) r ≫
      Functor.whiskerLeft (𝟭 C) mc = nc := h

private theorem weakViaForget {U V C : Type}
    [SmallCategory U] [SmallCategory V] [SmallCategory C]
    (p : U ⥤ V) (q : V ⥤ C) (r : U ⥤ C) (e : p ⋙ q = r)
    (hq : WeakEquivalence (nerveMap q)) (hr : WeakEquivalence (nerveMap r)) :
    WeakEquivalence (nerveMap p) := by
  letI := hq
  apply (weakEquivalence_postcomp_iff (nerveMap p) (nerveMap q)).mp
  change WeakEquivalence (nerveMap (p ⋙ q))
  rw [e]
  exact hr

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The original shared insertion choices, without new graph or triangle choices. -/
abbrev Index := JTSharedInsertionChoices.Index F j

private abbrev oldFamily := JTSharedInsertionNormalizedSeam.oldFamily F j
private abbrev coarseFamily := JTSharedInsertionCoarseLabels.family F j
private abbrev N := (oldFamily F j).labels
private abbrev M := JTSharedInsertionCoarseLabels.labels F j
private abbrev t := JTSharedInsertionCoarseGraph.oldTime F j
private abbrev nc := JTSharedInsertionOldGraph.target F j
private abbrev mc := JTSharedInsertionCoarseNative.target F j
private abbrev np := JTSharedInsertionOldGraph.projection F j
private abbrev mp := JTSharedInsertionCoarseGraph.projection F j
private abbrev nq := JTSharedInsertionOldGraph.parameter F j
private abbrev mq := JTSharedInsertionCoarseGraph.parameter F j
private abbrev r := JTSharedInsertionCoarseDecoratedComparison.comparison F j
private abbrev eta := JTSharedInsertionCoarseGraphComparison.map F j
private abbrev P := JTSharedInsertionSeamSurroundings.leftNative F j
private abbrev R := JTSharedInsertionSeamSurroundings.rightNative F j
private abbrev K := JTSharedInsertionChoices.ordinals F j

private theorem graph_square : eta F j ≫ mp F j = np F j ≫
    JTSharedInsertionPhaseGraph.mapWithTime (JTWhiskeredSeamTarget.nativeOf (r F j))
      (t F j) := by
  rw [JTSharedInsertionCoarseDecoratedComparison.native_comparison]
  exact JTSharedInsertionCoarseGraphComparison.map_projection F j

private def oldRaw :=
  family_rawEquation (P := P F j) (R := R F j) (K := K F j)
    (M := NecklaceCode.single 0) Q (oldFamily F j) (t F j) (nc F j)
    (np F j) (nq F j) (JTSharedInsertionOldRaw.ordered_raw F j)

private def trace_square (p : Index F j) :=
  trace_coordinate (P := P F j) (R := R F j)
    (P' := JTSharedInsertionCoarseLabels.leftNative F j)
    (M' := JTSharedInsertionCoarseLabels.middleNative F j)
    (R' := JTSharedInsertionCoarseLabels.rightNative F j)
    (K := K F j) (M := NecklaceCode.single 0) (oldFamily F j) (coarseFamily F j)
    (nq F j) (mq F j) (r F j) (eta F j)
    (JTSharedInsertionCoarseGraphComparison.map_parameter F j)
    (JTSharedInsertionCoarseDecoratedComparison.coefficient_comparison F j) p

private def target_square :=
  target_identity (r F j) (nc F j) (mc F j)
    (JTSharedInsertionCoarseDecoratedComparison.target_square F j)

private theorem old_evaluation_eq : JTSharedInsertionOldRaw.evaluation F j =
    JTGraphCoveredLabelEvaluation.evaluation Q (N F j) (t F j) (nc F j)
      (newProjection Q (N F j) (t F j) (nc F j) (np F j)) (nq F j) (oldRaw F j) := by
  unfold JTSharedInsertionOldRaw.evaluation
  exact family_evaluation_eq (P := P F j) (R := R F j) (K := K F j)
    (M := NecklaceCode.single 0) Q (oldFamily F j) (t F j) (nc F j)
    (JTSharedInsertionOldRaw.projectionTarget F j) (nq F j) _ (oldRaw F j)

private def actualSourceChange :=
  fullSourceChange Q (N F j) (M F j) (t F j) (nc F j) (mc F j)
    (np F j) (mp F j) (r F j) (eta F j) (graph_square F j)

private def actualSourceChange_cylinder (p : Index F j) :=
  fullSourceChange_cylinder Q (N F j) (M F j) (t F j) (nc F j) (mc F j)
    (np F j) (mp F j) (r F j) (eta F j) (graph_square F j) p

private def actualPresentation :=
  fullPresentation Q (N F j) (M F j) (t F j) (nc F j) (mc F j)
    (np F j) (mp F j) (r F j) (eta F j) (graph_square F j)

/-- Transport the complete inverse images of BOTH original endpoint lines. -/
def sourceChange : JTSharedInsertionOldRaw.reduced F j ⟶
    JTSharedInsertionCoarseEvaluation.reduced F j :=
  actualSourceChange F j

/-- The ENTIRE original-time graph summand is preserved by the reduced source map. -/
theorem sourceChange_cylinder (p : Index F j) :
    (JTGraphCoveredCylinderEquations.inc Q (N F j) (t F j) (nc F j)
      (JTSharedInsertionOldRaw.projectionTarget F j)).app p ≫
        ((sourceChange F j).app p).right =
      (eta F j).app p ≫ (JTSharedInsertionCoarseEvaluation.cylinderInclusion F j).app p :=
  actualSourceChange_cylinder F j p

/-- Keep every internal necklace and operator under the exact full source change. -/
def presentation : BoundaryNecklaceComma.Presentation (JTSharedInsertionOldRaw.reduced F j) ⥤
    BoundaryNecklaceComma.Presentation (JTSharedInsertionCoarseEvaluation.reduced F j) :=
  actualPresentation F j

/-- Evaluate ALL internal necklaces in the SAME original Q with its global endpoints. -/
def comparison : JTSharedInsertionOldRaw.evaluation F j ⟶
    presentation F j ⋙ JTSharedInsertionCoarseEvaluation.evaluation F j := by
  rw [old_evaluation_eq]
  exact fullComparison Q (N F j) (M F j) (t F j) (nc F j) (mc F j)
    (np F j) (mp F j) (r F j) (eta F j) (graph_square F j) (nq F j) (mq F j)
    (trace_square F j) (target_square F j) (oldRaw F j)
    (JTSharedInsertionCoarseEvaluation.rawEquation F j)

/-- The comparison retains exactly the SAME shared insertion source. -/
theorem presentation_toChoices : presentation F j ⋙
    JTSharedInsertionCoarseEvaluation.toChoices F j = JTSharedInsertionOldRaw.toChoices F j :=
  fullPresentation_forget Q (N F j) (M F j) (t F j) (nc F j) (mc F j)
    (np F j) (mp F j) (r F j) (eta F j) (graph_square F j)

/-- Weakness follows ONLY over Shared.Index from the exact forget triangle. -/
theorem presentation_weak : WeakEquivalence (nerveMap (presentation F j)) :=
  weakViaForget (presentation F j) (JTSharedInsertionCoarseEvaluation.toChoices F j)
    (JTSharedInsertionOldRaw.toChoices F j) (presentation_toChoices F j)
    (JTSharedInsertionCoarseEvaluation.toChoices_weak F j)
    (JTSharedInsertionOldRaw.toChoices_weak F j)

end
end DaggerModels.PartII.JTSharedInsertionCoarseEvaluationComparison
