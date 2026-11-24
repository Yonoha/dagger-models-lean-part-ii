import DaggerModelsPartII.JTSharedInsertionOldRaw
import DaggerModelsPartII.JTGraphCoveredRawTransport
import DaggerModelsPartII.JTGraphCoveredLiftComparison
import DaggerModelsPartII.JTSharedInsertionPhaseGraph
import DaggerModelsPartII.JTPrismChainGraphReindex
import DaggerModelsPartII.JTReindexedEndpointCoverTransport
import DaggerModelsPartII.JTGraphCoveredComparisonEquations
import DaggerModelsPartII.JTBoundaryNecklaceTwoReindexComparison

/-!
# Complete graph transport from the collapsed insertion to the corrected old split

The coefficient operator is the actual triangle-chain projection to the shared
chain. Every lifted parameter assignment maps canonically, and source reindexing
uses the checked full graph isomorphism. The old label is the corrected P + point
+ R family with the original Q and global endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionOldComparison

noncomputable section

private abbrev J := GroupoidSimplex.parameter

private def liftMap {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) (Y : B ⥤ SSet.{0}) {k m : B ⥤ SimplexCategory}
    (p : Y ⟶ k ⋙ J) (α : m ⟶ k) (X : I ⥤ SSet.{0})
    (c : X ⟶ G ⋙ Y) (q : X ⟶ (G ⋙ m) ⋙ J)
    (hq : q ≫ Functor.whiskerRight (Functor.whiskerLeft G α) J =
      c ≫ Functor.whiskerLeft G p) : X ⟶ G ⋙ JTPrismChainGraphCover.cover Y p α :=
  JTPrismChainGraphTransport.lift (k := G ⋙ k) (m := G ⋙ m) (G ⋙ Y) (Functor.whiskerLeft G p)
    (Functor.whiskerLeft G α) X c q hq ≫ JTPrismChainGraphReindex.reindex G Y p α

private theorem liftMap_projection {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) (Y : B ⥤ SSet.{0}) {k m : B ⥤ SimplexCategory}
    (p : Y ⟶ k ⋙ J) (α : m ⟶ k) (X : I ⥤ SSet.{0})
    (c : X ⟶ G ⋙ Y) (q : X ⟶ (G ⋙ m) ⋙ J)
    (hq : q ≫ Functor.whiskerRight (Functor.whiskerLeft G α) J =
      c ≫ Functor.whiskerLeft G p) :
    liftMap G Y p α X c q hq ≫
      Functor.whiskerLeft G (JTPrismChainGraphCover.projection Y p α) = c := by
  rw [liftMap, Category.assoc, JTPrismChainGraphReindex.reindex_projection,
    JTPrismChainGraphTransport.lift_projection]

private theorem liftMap_parameter {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) (Y : B ⥤ SSet.{0}) {k m : B ⥤ SimplexCategory}
    (p : Y ⟶ k ⋙ J) (α : m ⟶ k) (X : I ⥤ SSet.{0})
    (c : X ⟶ G ⋙ Y) (q : X ⟶ (G ⋙ m) ⋙ J)
    (hq : q ≫ Functor.whiskerRight (Functor.whiskerLeft G α) J =
      c ≫ Functor.whiskerLeft G p) :
    liftMap G Y p α X c q hq ≫
      Functor.whiskerLeft G (JTPrismChainGraphCover.parameter Y p α) = q := by
  rw [liftMap, Category.assoc, JTPrismChainGraphReindex.reindex_parameter,
    JTPrismChainGraphTransport.lift_parameter]

private def retarget {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) {X X' : I ⥤ SSet.{0}} {Y Y' : B ⥤ SSet.{0}}
    (eX : X ≅ X') (eY : Y ≅ Y') (c : X ⟶ G ⋙ Y) : X' ⟶ G ⋙ Y' :=
  eX.inv ≫ c ≫ Functor.whiskerLeft G eY.hom

private theorem retarget_square {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) {X X' Z : I ⥤ SSet.{0}} {Y Y' U : B ⥤ SSet.{0}}
    (eX : X ≅ X') (eY : Y ≅ Y') (c : X ⟶ G ⋙ Y)
    (πX : Z ⟶ X) (πY : U ⟶ Y) (η : Z ⟶ G ⋙ U)
    (hπ : η ≫ Functor.whiskerLeft G πY = πX ≫ c) :
    η ≫ Functor.whiskerLeft G (πY ≫ eY.hom) =
      (πX ≫ eX.hom) ≫ retarget G eX eY c := by
  rw [Functor.whiskerLeft_comp, ← Category.assoc, hπ]
  simp only [retarget, Category.assoc, Iso.hom_inv_id_assoc]

private theorem product_projection_app {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) (U : NecklaceCode)
    {B : SSet.{0}} (q : U.toSSet ⟶ B) (c : N ⟶ (Functor.const C).obj U)
    {Y : C ⥤ SSet.{0}} (π : Y ⟶ JTGraphCoveredProductInterface.product N t) (a : C) :
    ((π ≫ (JTGraphCoveredProductInterface.iso N t U q c).hom).app a :
      Y.obj a ⟶ (N.obj a).toSSet ⊗ J.obj (t.obj a)) = π.app a := by
  simp only [NatTrans.comp_app, JTGraphCoveredProductInterface.iso_hom_app,
    Category.comp_id]

private theorem product_projection_trivial {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) (U : NecklaceCode)
    {B : SSet.{0}} (q : U.toSSet ⟶ B) (c : N ⟶ (Functor.const C).obj U)
    {Y : C ⥤ SSet.{0}} (π : Y ⟶ JTGraphCoveredProductInterface.product N t)
    (hπ : ∀ a, trivialFibrations SSet.{0} (π.app a)) (a : C) :
    trivialFibrations SSet.{0}
      ((π ≫ (JTGraphCoveredProductInterface.iso N t U q c).hom).app a) := by
  rw [product_projection_app]
  exact hπ a

private theorem product_iso_inv_app {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) (U : NecklaceCode)
    {B : SSet.{0}} (q : U.toSSet ⟶ B) (c : N ⟶ (Functor.const C).obj U) (a : C) :
    (JTGraphCoveredProductInterface.iso N t U q c).inv.app a = 𝟙 _ := rfl

private theorem retarget_product_app {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) (N : I ⥤ NecklaceCode) (M : B ⥤ NecklaceCode)
    (t : B ⥤ SimplexCategory) (U : NecklaceCode) {V : SSet.{0}} (q : U.toSSet ⟶ V)
    (n : N ⟶ (Functor.const I).obj U) (m : M ⟶ (Functor.const B).obj U)
    (c : JTGraphCoveredProductInterface.product N (G ⋙ t) ⟶
      G ⋙ JTGraphCoveredProductInterface.product M t) (a : I) :
    ((retarget G (JTGraphCoveredProductInterface.iso N (G ⋙ t) U q n)
        (JTGraphCoveredProductInterface.iso M t U q m) c).app a :
      (N.obj a).toSSet ⊗ J.obj (t.obj (G.obj a)) ⟶
        (M.obj (G.obj a)).toSSet ⊗ J.obj (t.obj (G.obj a))) = c.app a := by
  simp only [retarget, NatTrans.comp_app, Functor.whiskerLeft_app,
    product_iso_inv_app, JTGraphCoveredProductInterface.iso_hom_app, Category.id_comp]
  exact Category.comp_id _

private theorem endpoint_tensor {T U : NecklaceCode} (f : T ⟶ U) (t : SimplexCategory) :
    (JTNecklaceEndpointCylinder.endpointInclusion T ⊗ₘ 𝟙 (J.obj t)) ≫
        (f.map ⊗ₘ 𝟙 (J.obj t)) =
      JTNecklaceEndpointCylinder.endpointInclusion U ⊗ₘ 𝟙 (J.obj t) := by
  rw [tensorHom_comp_tensorHom, Category.id_comp,
    JTNecklaceEndpointCylinder.endpointInclusion_natural]

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Boundary := JTXiEndpointCollapse.boundary

private def nativePart {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x y : Vertex W} (G : I ⥤ B)
    {N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
    {M : B ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ G ⋙ M) :
    JTParametrizedTargetFamilies.codes N ⟶ G ⋙ JTParametrizedTargetFamilies.codes M :=
  Functor.whiskerRight r
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y) ⋙
      CategoryTheory.Prod.fst NecklaceCode SimplexCategory)

private def degreePart {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x y : Vertex W} (G : I ⥤ B)
    {N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
    {M : B ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ G ⋙ M) :
    JTParametrizedTargetFamilyComparison.degrees N ⟶
      G ⋙ JTParametrizedTargetFamilyComparison.degrees M :=
  Functor.whiskerRight r
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y) ⋙
      CategoryTheory.Prod.snd NecklaceCode SimplexCategory)

private theorem native_coordinate {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) (N : I ⥤ NecklaceCode) (M : B ⥤ NecklaceCode) (t : B ⥤ SimplexCategory)
    {X : I ⥤ SSet.{0}} {Y : B ⥤ SSet.{0}}
    (πX : X ⟶ JTGraphCoveredProductInterface.product N (G ⋙ t))
    (πY : Y ⟶ JTGraphCoveredProductInterface.product M t)
    (η : X ⟶ G ⋙ Y) (κ : N ⟶ G ⋙ M)
    (hπ : η ≫ Functor.whiskerLeft G πY =
      πX ≫ JTSharedInsertionPhaseGraph.reindexedProductMap G κ t) (a : I) :
    (πX.app a ≫ fst (N.obj a).toSSet (J.obj (t.obj (G.obj a)))) ≫ (κ.app a).map =
      η.app a ≫ πY.app (G.obj a) ≫ fst (M.obj (G.obj a)).toSSet
        (J.obj (t.obj (G.obj a))) := by
  have h := congrArg (· ≫ fst (M.obj (G.obj a)).toSSet (J.obj (t.obj (G.obj a))))
    (NatTrans.congr_app hπ a)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    JTSharedInsertionPhaseGraph.reindexedProductMap_app, Category.assoc, tensorHom_fst]
      using h.symm

private abbrev rawEquation {C : Type} [SmallCategory C] {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (N : C ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : C ⥤ SimplexCategory)
    (c : JTParametrizedTargetFamilies.codes N ⟶ (Functor.const C).obj Q.code)
    {X : C ⥤ SSet.{0}}
    (π : X ⟶ JTGraphCoveredProductInterface.product (JTParametrizedTargetFamilies.codes N) t)
    (θ : X ⟶ JTParametrizedTargetFamilyComparison.degrees N ⋙ J) (a : C) :=
  lift (π.app a ≫ fst ((JTParametrizedTargetFamilies.codes N).obj a).toSSet (J.obj (t.obj a)))
      (θ.app a) ≫ JTNecklaceLabelRealization.realizedLabel
        ((JTParametrizedTargetFamilies.codes N).obj a).toSSet W
        ((JTParametrizedTargetFamilyComparison.degrees N).obj a)
        (JTRealizedLabelEndpoints.orderedLabel W x y
          ((JTParametrizedTargetFamilies.codes N).obj a)
          ((JTParametrizedTargetFamilyComparison.degrees N).obj a)
          (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            (N.obj a))) =
    (π.app a ≫ fst ((JTParametrizedTargetFamilies.codes N).obj a).toSSet (J.obj (t.obj a))) ≫
      (c.app a).map ≫ Q.map

private theorem raw_to_target {C : Type} [SmallCategory C] {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (N : C ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : C ⥤ SimplexCategory)
    (c : JTParametrizedTargetFamilies.codes N ⟶ (Functor.const C).obj Q.code)
    {X : C ⥤ SSet.{0}}
    (π : X ⟶ JTGraphCoveredProductInterface.product (JTParametrizedTargetFamilies.codes N) t)
    (θ : X ⟶ JTParametrizedTargetFamilyComparison.degrees N ⋙ J)
    (H : ∀ a, rawEquation Q N t c π θ a) :
    JTGraphCoveredLiftComparison.RawEquation Q N t c
      (π ≫ (JTGraphCoveredProductInterface.iso (JTParametrizedTargetFamilies.codes N)
        t Q.code Q.map c).hom) θ := by
  intro a
  rw [product_projection_app]
  exact H a

private def NativeEquation {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (G : I ⥤ B)
    (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (M : B ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (nt : I ⥤ SimplexCategory) (mt : B ⥤ SimplexCategory)
    (nc : JTParametrizedTargetFamilies.codes N ⟶ (Functor.const I).obj Q.code)
    (mc : JTParametrizedTargetFamilies.codes M ⟶ (Functor.const B).obj Q.code)
    {X : I ⥤ SSet.{0}} {Y : B ⥤ SSet.{0}}
    (np : X ⟶ JTJointRelativeParameters.withTime Q.map J nt
      (Over.lift (JTParametrizedTargetFamilies.codes N) nc)
      (JTTargetIntervalOverMapping.whole Q.code))
    (mp : Y ⟶ JTJointRelativeParameters.withTime Q.map J mt
      (Over.lift (JTParametrizedTargetFamilies.codes M) mc)
      (JTTargetIntervalOverMapping.whole Q.code))
    (r : N ⟶ G ⋙ M) (η : X ⟶ G ⋙ Y) (a : I) : Prop :=
  (np.app a ≫ fst ((JTParametrizedTargetFamilies.codes N).obj a).toSSet
      (J.obj (nt.obj a))) ≫
    ((JTGraphCoveredEvaluationSquares.nativePart (N := N) (M := M) G r).app a).map =
  η.app a ≫ mp.app (G.obj a) ≫ fst
    ((JTParametrizedTargetFamilies.codes M).obj (G.obj a)).toSSet (J.obj (mt.obj (G.obj a)))

private theorem target_native_coordinate {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (G : I ⥤ B)
    (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (M : B ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : B ⥤ SimplexCategory)
    (nc : JTParametrizedTargetFamilies.codes N ⟶ (Functor.const I).obj Q.code)
    (mc : JTParametrizedTargetFamilies.codes M ⟶ (Functor.const B).obj Q.code)
    {X : I ⥤ SSet.{0}} {Y : B ⥤ SSet.{0}}
    (np : X ⟶ JTGraphCoveredProductInterface.product (JTParametrizedTargetFamilies.codes N)
      (G ⋙ t))
    (mp : Y ⟶ JTGraphCoveredProductInterface.product (JTParametrizedTargetFamilies.codes M) t)
    (r : N ⟶ G ⋙ M) (η : X ⟶ G ⋙ Y)
    (hπ : η ≫ Functor.whiskerLeft G mp = np ≫
      JTSharedInsertionPhaseGraph.reindexedProductMap G (nativePart G r) t) (a : I) :
    (((np ≫ (JTGraphCoveredProductInterface.iso (JTParametrizedTargetFamilies.codes N)
        (G ⋙ t) Q.code Q.map nc).hom).app a) ≫
        fst ((JTParametrizedTargetFamilies.codes N).obj a).toSSet (J.obj (t.obj (G.obj a)))) ≫
      ((JTGraphCoveredEvaluationSquares.nativePart G r).app a).map =
    η.app a ≫ ((mp ≫ (JTGraphCoveredProductInterface.iso
        (JTParametrizedTargetFamilies.codes M) t Q.code Q.map mc).hom).app (G.obj a)) ≫
      fst ((JTParametrizedTargetFamilies.codes M).obj (G.obj a)).toSSet
        (J.obj (t.obj (G.obj a))) := by
  rw [product_projection_app, product_projection_app]
  exact native_coordinate G (JTParametrizedTargetFamilies.codes N)
    (JTParametrizedTargetFamilies.codes M) t np mp η (nativePart G r) hπ a

private theorem family_rawEquation {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    {M : NecklaceCode}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (G : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    (t : C ⥤ SimplexCategory)
    (c : JTParametrizedTargetFamilies.codes G.labels ⟶ (Functor.const C).obj Q.code)
    {X : C ⥤ SSet.{0}}
    (π : X ⟶ JTGraphCoveredProductInterface.product
      (JTParametrizedTargetFamilies.codes G.labels) t) (θ : X ⟶ K ⋙ J)
    (H : ∀ a, JTWhiskeredGraphRaw.PieceEquations W (G.data a)
      (π.app a ≫ fst _ _) (θ.app a) ((c.app a).map ≫ Q.map)) (a : C) :
    rawEquation Q G.labels t c π θ a :=
  JTWhiskeredGraphRaw.PieceEquations.ordered_raw W (G.data a) (H a)

private theorem transport_raw {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (G : I ⥤ B)
    (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (M : B ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : B ⥤ SimplexCategory)
    (cN : JTParametrizedTargetFamilies.codes N ⟶ (Functor.const I).obj Q.code)
    (cM : JTParametrizedTargetFamilies.codes M ⟶ (Functor.const B).obj Q.code)
    (r : N ⟶ G ⋙ M) {X : I ⥤ SSet.{0}} {Y : B ⥤ SSet.{0}}
    (πX : X ⟶ JTGraphCoveredProductInterface.product (JTParametrizedTargetFamilies.codes N)
      (G ⋙ t))
    (πY : Y ⟶ JTGraphCoveredProductInterface.product (JTParametrizedTargetFamilies.codes M) t)
    (η : X ⟶ G ⋙ Y)
    (θX : X ⟶ JTParametrizedTargetFamilyComparison.degrees N ⋙ J)
    (θY : Y ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
    (hπ : η ≫ Functor.whiskerLeft G πY =
      πX ≫ JTSharedInsertionPhaseGraph.reindexedProductMap G (nativePart G r) t)
    (hθ : η ≫ Functor.whiskerLeft G θY = θX ≫ Functor.whiskerRight (degreePart G r) J)
    (hc : nativePart G r ≫ Functor.whiskerLeft G cM = cN)
    (hOld : ∀ b, rawEquation Q M t cM πY θY b) (a : I) :
    rawEquation Q N (G ⋙ t) cN πX θX a := by
  have hn := native_coordinate G (JTParametrizedTargetFamilies.codes N)
    (JTParametrizedTargetFamilies.codes M) t πX πY η (nativePart G r) hπ a
  have hq : θX.app a ≫ J.map
      ((OrderedLabelElements.projection W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map (r.app a)).2 =
      η.app a ≫ θY.app (G.obj a) := (NatTrans.congr_app hθ a).symm
  have hr := JTGraphCoveredRawTransport.ordered_raw (r.app a)
    (πX.app a ≫ fst _ _) (θX.app a) (πY.app (G.obj a) ≫ fst _ _) (θY.app (G.obj a))
    (η.app a) ((cM.app (G.obj a)).map ≫ Q.map) hn hq (hOld (G.obj a))
  have hf : ((nativePart G r).app a).map ≫ (cM.app (G.obj a)).map ≫ Q.map =
      (cN.app a).map ≫ Q.map := by
    change (((nativePart G r).app a) ≫ cM.app (G.obj a)).map ≫ Q.map = _
    exact congrArg (fun f ↦ f.map ≫ Q.map) (NatTrans.congr_app hc a)
  exact hr.trans (by
    simpa only [Category.assoc] using congrArg ((πX.app a ≫ fst _ _) ≫ ·) hf)

private theorem native_target_paste {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) {N : I ⥤ NecklaceCode} {M T V : B ⥤ NecklaceCode}
    (κ : N ⟶ G ⋙ M) (n : M ⟶ T) (c : T ⟶ V) :
    κ ≫ Functor.whiskerLeft G (n ≫ c) =
      (κ ≫ Functor.whiskerLeft G n) ≫ Functor.whiskerLeft G c := by
  rw [Functor.whiskerLeft_comp, Category.assoc]

private theorem boundary_retarget {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (G : I ⥤ B)
    (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (M : B ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : B ⥤ SimplexCategory)
    (n : JTParametrizedTargetFamilies.codes N ⟶ (Functor.const I).obj Q.code)
    (m : JTParametrizedTargetFamilies.codes M ⟶ (Functor.const B).obj Q.code)
    (κ : JTParametrizedTargetFamilies.codes N ⟶ G ⋙ JTParametrizedTargetFamilies.codes M) :
    JTGraphCoveredLabelEvaluation.boundary Q N (G ⋙ t) n ≫
        retarget G
          (JTGraphCoveredProductInterface.iso (JTParametrizedTargetFamilies.codes N)
            (G ⋙ t) Q.code Q.map n)
          (JTGraphCoveredProductInterface.iso (JTParametrizedTargetFamilies.codes M)
            t Q.code Q.map m)
          (JTSharedInsertionPhaseGraph.reindexedProductMap G κ t) =
      (Functor.associator G t JTXiEndpointCollapse.boundaryCylinder).hom ≫
        Functor.whiskerLeft G (JTGraphCoveredLabelEvaluation.boundary Q M t m) := by
  apply NatTrans.ext
  funext p
  change (JTNecklaceEndpointCylinder.endpointInclusion
      ((JTParametrizedTargetFamilies.codes N).obj p) ⊗ₘ 𝟙 (J.obj (t.obj (G.obj p)))) ≫
      (retarget G
        (JTGraphCoveredProductInterface.iso (JTParametrizedTargetFamilies.codes N)
          (G ⋙ t) Q.code Q.map n)
        (JTGraphCoveredProductInterface.iso (JTParametrizedTargetFamilies.codes M)
          t Q.code Q.map m)
        (JTSharedInsertionPhaseGraph.reindexedProductMap G κ t)).app p =
      𝟙 _ ≫ (JTNecklaceEndpointCylinder.endpointInclusion
        ((JTParametrizedTargetFamilies.codes M).obj (G.obj p)) ⊗ₘ
          𝟙 (J.obj (t.obj (G.obj p))))
  rw [retarget_product_app, JTSharedInsertionPhaseGraph.reindexedProductMap_app]
  exact (endpoint_tensor (κ.app p) (t.obj (G.obj p))).trans (Category.id_comp _).symm

open JTParametrizedTargetFamilies (Family codes)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The original actual triangle choices and all final coefficient-chain operators. -/
abbrev Index := JTSharedInsertionPhaseGraph.Index F j

/-- The actual projection retaining the complete shared correction choices. -/
abbrev base := JTSharedInsertionPhaseGraph.base F j

private theorem collapsed_parameter_projection :
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        JTSharedInsertionNormalizedSeam.oldDegrees F j ⋙ J from
      JTSharedInsertionPhaseGraph.collapsedTrace F j ≫ Functor.whiskerRight
        (JTSharedInsertionNormalizedSeam.coefficientProjection F j) J) =
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        JTSharedInsertionNormalizedSeam.oldDegrees F j ⋙ J from
      JTSharedInsertionPhaseGraph.collapsedProjection F j ≫
        JTSharedInsertionPhaseGraph.coarseParameter F j
          (𝟙 (JTSharedInsertionPhaseGraph.collapsedCodes F j))) :=
  JTPrismChainGraphCover.parameter_projection
    (k := JTSharedInsertionNormalizedSeam.oldDegrees F j)
    (m := JTSharedInsertionSeamTriangles.ordinals F j)
    (JTSharedInsertionPhaseGraph.X F j (JTSharedInsertionPhaseGraph.collapsedCodes F j))
    (JTSharedInsertionPhaseGraph.coarseParameter F j
      (𝟙 (JTSharedInsertionPhaseGraph.collapsedCodes F j)))
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j)

private theorem lift_parameter_square :
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        (base F j ⋙ JTSharedInsertionOldGraph.oldDegrees F j) ⋙ J from
      (JTSharedInsertionPhaseGraph.collapsedTrace F j ≫
        Functor.whiskerRight (JTSharedInsertionSeamTriangles.toOld F j) J) ≫
        Functor.whiskerRight (Functor.whiskerLeft (base F j)
          (JTSharedInsertionOldGraph.coefficientProjection F j)) J) =
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        (base F j ⋙ JTSharedInsertionOldGraph.oldDegrees F j) ⋙ J from
      (JTSharedInsertionPhaseGraph.collapsedProjection F j ≫
        JTSharedInsertionPhaseGraph.oldProductMap F j) ≫
        Functor.whiskerLeft (base F j) (JTSharedInsertionOldGraph.coarseParameter F j)) := by
  rw [Category.assoc, ← Functor.whiskerRight_comp]
  change JTSharedInsertionPhaseGraph.collapsedTrace F j ≫
    Functor.whiskerRight (JTSharedInsertionNormalizedSeam.coefficientProjection F j) J = _
  have h := collapsed_parameter_projection F j
  rw [JTSharedInsertionPhaseGraph.collapsed_coarseParameter] at h
  simpa only [JTSharedInsertionPhaseGraph.collapsedParameter, Category.assoc] using h

/-- Every final coefficient lift maps to its shared-chain image on the full old graph. -/
def toOld : JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
    base F j ⋙ JTSharedInsertionOldGraph.graph F j :=
  liftMap (k := JTSharedInsertionOldGraph.oldDegrees F j)
    (m := JTSharedInsertionChoices.ordinals F j)
    (base F j) (JTSharedInsertionOldGraph.X F j)
    (JTSharedInsertionOldGraph.coarseParameter F j)
    (JTSharedInsertionOldGraph.coefficientProjection F j)
    (JTSharedInsertionPhaseGraph.collapsedGraph F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j ≫
      JTSharedInsertionPhaseGraph.oldProductMap F j)
    (JTSharedInsertionPhaseGraph.collapsedTrace F j ≫
      Functor.whiskerRight (JTSharedInsertionSeamTriangles.toOld F j) J)
    (lift_parameter_square F j)

/-- The whole original native/time projection commutes before endpoint collapse. -/
theorem toOld_projection :
    toOld F j ≫ Functor.whiskerLeft (base F j) (JTSharedInsertionOldGraph.projection F j) =
      JTSharedInsertionPhaseGraph.collapsedProjection F j ≫
        JTSharedInsertionPhaseGraph.oldProductMap F j :=
  liftMap_projection (k := JTSharedInsertionOldGraph.oldDegrees F j)
    (m := JTSharedInsertionChoices.ordinals F j)
    (base F j) (JTSharedInsertionOldGraph.X F j)
    (JTSharedInsertionOldGraph.coarseParameter F j)
    (JTSharedInsertionOldGraph.coefficientProjection F j)
    (JTSharedInsertionPhaseGraph.collapsedGraph F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j ≫
      JTSharedInsertionPhaseGraph.oldProductMap F j)
    (JTSharedInsertionPhaseGraph.collapsedTrace F j ≫
      Functor.whiskerRight (JTSharedInsertionSeamTriangles.toOld F j) J)
    (lift_parameter_square F j)

/-- The complete lifted coefficient parameter changes by the actual triangle projection. -/
theorem toOld_parameter :
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        (base F j ⋙ JTSharedInsertionChoices.ordinals F j) ⋙ J from
      toOld F j ≫ Functor.whiskerLeft (base F j) (JTSharedInsertionOldGraph.parameter F j)) =
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        (base F j ⋙ JTSharedInsertionChoices.ordinals F j) ⋙ J from
      JTSharedInsertionPhaseGraph.collapsedTrace F j ≫
        Functor.whiskerRight (JTSharedInsertionSeamTriangles.toOld F j) J) :=
  liftMap_parameter (k := JTSharedInsertionOldGraph.oldDegrees F j)
    (m := JTSharedInsertionChoices.ordinals F j)
    (base F j) (JTSharedInsertionOldGraph.X F j)
    (JTSharedInsertionOldGraph.coarseParameter F j)
    (JTSharedInsertionOldGraph.coefficientProjection F j)
    (JTSharedInsertionPhaseGraph.collapsedGraph F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j ≫
      JTSharedInsertionPhaseGraph.oldProductMap F j)
    (JTSharedInsertionPhaseGraph.collapsedTrace F j ≫
      Functor.whiskerRight (JTSharedInsertionSeamTriangles.toOld F j) J)
    (lift_parameter_square F j)

private abbrev collapsedFamily := JTWhiskeredSeamDiagram.collapsedFamily
  (JTSharedInsertionNormalizedSeam.seamFamily F j)
private abbrev oldFamily := JTSharedInsertionOldGraph.oldFamily F j
private abbrev newIso := JTGraphCoveredProductInterface.iso
  (JTSharedInsertionPhaseGraph.collapsedCodes F j) (JTSharedInsertionPhaseGraph.oldTime F j)
  Q.code Q.map (JTSharedInsertionSeamNative.collapsedTarget F j)
private abbrev oldIso := JTGraphCoveredProductInterface.iso
  (codes (oldFamily F j).labels) (JTSharedInsertionOldGraph.oldTime F j)
  Q.code Q.map (JTSharedInsertionOldGraph.target F j)

/-- The actual whole collapsed graph is read over the unchanged original Q. -/
def projectionTarget : JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
    JTWhiskeredGraphEvaluation.productDiagram Q (collapsedFamily F j)
      (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j) :=
  JTSharedInsertionPhaseGraph.collapsedProjection F j ≫ (newIso F j).hom

private abbrev productChange := retarget (base F j) (newIso F j) (oldIso F j)
  (JTSharedInsertionPhaseGraph.oldProductMap F j)

private theorem projection_target_square :
    toOld F j ≫ Functor.whiskerLeft (base F j) (JTSharedInsertionOldRaw.projectionTarget F j) =
      projectionTarget F j ≫ productChange F j :=
  retarget_square (base F j) (newIso F j) (oldIso F j)
    (JTSharedInsertionPhaseGraph.oldProductMap F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j)
    (JTSharedInsertionOldGraph.projection F j) (toOld F j) (toOld_projection F j)

private abbrev oldBoundary := JTGraphCoveredLabelEvaluation.boundary Q
  (oldFamily F j).labels (JTSharedInsertionOldGraph.oldTime F j)
    (JTSharedInsertionOldGraph.target F j)
private abbrev newBoundary := JTGraphCoveredLabelEvaluation.boundary Q
  (collapsedFamily F j).labels (JTSharedInsertionPhaseGraph.oldTime F j)
    (JTSharedInsertionSeamNative.collapsedTarget F j)
private abbrev oldEndpoint := Functor.whiskerLeft (JTSharedInsertionOldGraph.oldTime F j)
  JTXiEndpointCollapse.cylinderProjection
private abbrev newEndpoint := Functor.whiskerLeft (JTSharedInsertionPhaseGraph.oldTime F j)
  JTXiEndpointCollapse.cylinderProjection
private abbrev endpointMap := (Functor.associator (base F j)
  (JTSharedInsertionOldGraph.oldTime F j) JTXiEndpointCollapse.boundaryCylinder).hom

private theorem boundary_square :
    newBoundary F j ≫ productChange F j =
      endpointMap F j ≫ Functor.whiskerLeft (base F j) (oldBoundary F j) :=
  boundary_retarget Q (base F j) (collapsedFamily F j).labels (oldFamily F j).labels
    (JTSharedInsertionOldGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
    (JTSharedInsertionOldGraph.target F j) (JTSharedInsertionPhaseGraph.nativeToOld F j)

private theorem endpoint_square (p : Index F j) :
    (endpointMap F j).app p ≫ (oldEndpoint F j).app ((base F j).obj p) =
      (newEndpoint F j).app p := Category.id_comp _

/-- Collapse the entire inverse image of both original endpoint lines on the collapsed phase. -/
abbrev reduced := JTWhiskeredGraphEvaluation.reduced Q (collapsedFamily F j)
  (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
  (projectionTarget F j)

/-- The full reduced collapsed graph maps to the reindexed full corrected old graph. -/
def sourceChange : reduced F j ⟶ base F j ⋙ JTSharedInsertionOldRaw.reduced F j :=
  JTReindexedEndpointCoverTransport.sourceChange (base F j)
    (JTSharedInsertionOldRaw.projectionTarget F j) (oldBoundary F j) (oldEndpoint F j)
    (projectionTarget F j) (newBoundary F j) (newEndpoint F j)
    (productChange F j) (toOld F j) (endpointMap F j)
    (projection_target_square F j) (boundary_square F j) (endpoint_square F j)

private theorem comparison_degree :
    (show JTSharedInsertionSeamTriangles.ordinals F j ⟶
        base F j ⋙ JTSharedInsertionChoices.ordinals F j from
      degreePart (base F j) (JTSharedInsertionNormalizedSeam.collapsedToOld F j)) =
      JTSharedInsertionSeamTriangles.toOld F j := rfl

private theorem comparison_target :
    nativePart (base F j) (JTSharedInsertionNormalizedSeam.collapsedToOld F j) ≫
        Functor.whiskerLeft (base F j) (JTSharedInsertionOldGraph.target F j) =
      JTSharedInsertionSeamNative.collapsedTarget F j :=
  native_target_paste (base F j)
    (nativePart (base F j) (JTSharedInsertionNormalizedSeam.collapsedToOld F j))
    (JTSharedInsertionSeamNative.oldAssembly F j)
    (Functor.whiskerLeft (JTSharedInsertionChainSupport.originalBase F j) F.collapse)

private theorem trace_square :
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        (base F j ⋙ JTSharedInsertionChoices.ordinals F j) ⋙ J from
      toOld F j ≫ Functor.whiskerLeft (base F j) (JTSharedInsertionOldGraph.parameter F j)) =
    (show JTSharedInsertionPhaseGraph.collapsedGraph F j ⟶
        (base F j ⋙ JTSharedInsertionChoices.ordinals F j) ⋙ J from
      JTSharedInsertionPhaseGraph.collapsedTrace F j ≫ Functor.whiskerRight
        (degreePart (base F j) (JTSharedInsertionNormalizedSeam.collapsedToOld F j)) J) := by
  exact (toOld_parameter F j).trans (congrArg
    (fun v : JTSharedInsertionSeamTriangles.ordinals F j ⟶
        base F j ⋙ JTSharedInsertionChoices.ordinals F j ↦
      JTSharedInsertionPhaseGraph.collapsedTrace F j ≫ Functor.whiskerRight v J)
    (comparison_degree F j).symm)

-- Bound only the conversion between the two exact closed old-coordinate views.
set_option maxHeartbeats 850000 in
private theorem old_rawEquation (p : JTSharedInsertionOldGraph.Index F j) :
    rawEquation Q (oldFamily F j).labels (JTSharedInsertionOldGraph.oldTime F j)
      (JTSharedInsertionOldGraph.target F j) (JTSharedInsertionOldGraph.projection F j)
      (JTSharedInsertionOldGraph.parameter F j) p :=
  family_rawEquation (P := JTSharedInsertionSeamSurroundings.leftNative F j)
    (R := JTSharedInsertionSeamSurroundings.rightNative F j)
    (K := JTSharedInsertionChoices.ordinals F j) (M := single 0)
    (X := JTSharedInsertionOldGraph.graph F j) Q (oldFamily F j)
    (JTSharedInsertionOldGraph.oldTime F j) (JTSharedInsertionOldGraph.target F j)
    (JTSharedInsertionOldGraph.projection F j) (JTSharedInsertionOldGraph.parameter F j)
    (fun a ↦ JTSharedInsertionOldRaw.pieceEquations F j a) p

/-- The actual collapsed label has its complete ordered raw value in the original Q. -/
theorem ordered_raw (p : Index F j) : rawEquation Q (collapsedFamily F j).labels
    (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j)
    (JTSharedInsertionPhaseGraph.collapsedTrace F j) p :=
  transport_raw (X := JTSharedInsertionPhaseGraph.collapsedGraph F j)
    (Y := JTSharedInsertionOldGraph.graph F j) Q (base F j)
    (collapsedFamily F j).labels (oldFamily F j).labels
    (JTSharedInsertionOldGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
    (JTSharedInsertionOldGraph.target F j) (JTSharedInsertionNormalizedSeam.collapsedToOld F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j) (JTSharedInsertionOldGraph.projection F j)
    (toOld F j) (JTSharedInsertionPhaseGraph.collapsedTrace F j)
    (JTSharedInsertionOldGraph.parameter F j) (toOld_projection F j) (trace_square F j)
    (comparison_target F j) (old_rawEquation F j) p

private theorem target_raw : JTGraphCoveredLiftComparison.RawEquation Q
    (collapsedFamily F j).labels (JTSharedInsertionPhaseGraph.oldTime F j)
    (JTSharedInsertionSeamNative.collapsedTarget F j) (projectionTarget F j)
    (JTSharedInsertionPhaseGraph.collapsedTrace F j) :=
  raw_to_target (X := JTSharedInsertionPhaseGraph.collapsedGraph F j) Q
    (collapsedFamily F j).labels (JTSharedInsertionPhaseGraph.oldTime F j)
    (JTSharedInsertionSeamNative.collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j)
    (JTSharedInsertionPhaseGraph.collapsedTrace F j) (ordered_raw F j)

private theorem old_target_raw : JTGraphCoveredLiftComparison.RawEquation Q
    (oldFamily F j).labels (JTSharedInsertionOldGraph.oldTime F j)
    (JTSharedInsertionOldGraph.target F j) (JTSharedInsertionOldRaw.projectionTarget F j)
    (JTSharedInsertionOldGraph.parameter F j) :=
  raw_to_target (X := JTSharedInsertionOldGraph.graph F j) Q (oldFamily F j).labels
    (JTSharedInsertionOldGraph.oldTime F j) (JTSharedInsertionOldGraph.target F j)
    (JTSharedInsertionOldGraph.projection F j) (JTSharedInsertionOldGraph.parameter F j)
    (old_rawEquation F j)

/-- The actual collapsed whole graph lifts into the unchanged original fixed-Q diagram. -/
abbrev pullbackLift := JTGraphCoveredLiftInterface.pullbackLift Q (collapsedFamily F j).labels
  (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
  (projectionTarget F j) (JTSharedInsertionPhaseGraph.collapsedTrace F j) (target_raw F j)

/-- Evaluate all internal necklaces of the collapsed corrected label in the original Q. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTGraphCoveredLabelEvaluation.evaluation Q (collapsedFamily F j).labels
    (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
    (projectionTarget F j) (JTSharedInsertionPhaseGraph.collapsedTrace F j) (target_raw F j)

/-- This evaluates the complete pullback presentation, including every native operator. -/
theorem evaluation_eq_mapPresentation : evaluation F j =
    JTBoundaryNecklacePresentationCone.mapPresentation (JTTargetCommaPullback.diagram W x y Q)
      (reduced F j) (collapsedFamily F j).labels (pullbackLift F j) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  JTGraphCoveredLiftInterface.evaluation_eq_mapPresentation Q (collapsedFamily F j).labels
    (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
    (projectionTarget F j) (JTSharedInsertionPhaseGraph.collapsedTrace F j) (target_raw F j)

/-- The source change preserves the entire graph summand of the full endpoint quotient. -/
theorem sourceChange_cylinder (p : Index F j) :
    (JTGraphCoveredCylinderEquations.inc Q (collapsedFamily F j).labels
      (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
      (projectionTarget F j)).app p ≫ ((sourceChange F j).app p).right =
    (toOld F j).app p ≫ (JTGraphCoveredCylinderEquations.inc Q (oldFamily F j).labels
      (JTSharedInsertionOldGraph.oldTime F j) (JTSharedInsertionOldGraph.target F j)
      (JTSharedInsertionOldRaw.projectionTarget F j)).app ((base F j).obj p) :=
  JTReindexedEndpointCoverTransport.sourceChange_cylinder (base F j)
    (JTSharedInsertionOldRaw.projectionTarget F j) (oldBoundary F j) (oldEndpoint F j)
    (projectionTarget F j) (newBoundary F j) (newEndpoint F j)
    (productChange F j) (toOld F j) (endpointMap F j)
    (projection_target_square F j) (boundary_square F j) (endpoint_square F j) p

private theorem native_equation (p : Index F j) :
    NativeEquation (X := JTSharedInsertionPhaseGraph.collapsedGraph F j)
      (Y := JTSharedInsertionOldGraph.graph F j) Q (base F j)
      (collapsedFamily F j).labels (oldFamily F j).labels
      (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionOldGraph.oldTime F j)
      (JTSharedInsertionSeamNative.collapsedTarget F j) (JTSharedInsertionOldGraph.target F j)
      (projectionTarget F j) (JTSharedInsertionOldRaw.projectionTarget F j)
      (JTSharedInsertionNormalizedSeam.collapsedToOld F j) (toOld F j) p :=
  target_native_coordinate (X := JTSharedInsertionPhaseGraph.collapsedGraph F j)
    (Y := JTSharedInsertionOldGraph.graph F j) Q (base F j)
    (collapsedFamily F j).labels (oldFamily F j).labels (JTSharedInsertionOldGraph.oldTime F j)
    (JTSharedInsertionSeamNative.collapsedTarget F j) (JTSharedInsertionOldGraph.target F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j) (JTSharedInsertionOldGraph.projection F j)
    (JTSharedInsertionNormalizedSeam.collapsedToOld F j) (toOld F j) (toOld_projection F j) p

private theorem coefficient_equation (p : Index F j) :
    (JTSharedInsertionPhaseGraph.collapsedTrace F j).app p ≫
      J.map ((JTGraphCoveredEvaluationSquares.degreePart
        (N := (collapsedFamily F j).labels) (M := (oldFamily F j).labels) (base F j)
        (JTSharedInsertionNormalizedSeam.collapsedToOld F j)).app p) =
    (toOld F j).app p ≫ (JTSharedInsertionOldGraph.parameter F j).app ((base F j).obj p) :=
  (NatTrans.congr_app (trace_square F j) p).symm

/-- Change the whole endpoint quotient and base while retaining every internal necklace. -/
def toOldPresentation : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    BoundaryNecklaceComma.Presentation (JTSharedInsertionOldRaw.reduced F j) :=
  JTGraphCoveredLiftComparison.presentationMap Q (base F j)
    (collapsedFamily F j).labels (oldFamily F j).labels
    (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionOldGraph.oldTime F j)
    (JTSharedInsertionSeamNative.collapsedTarget F j) (JTSharedInsertionOldGraph.target F j)
    (projectionTarget F j) (JTSharedInsertionOldRaw.projectionTarget F j) (sourceChange F j)

/-- The collapsed and corrected old full evaluations compare naturally in the SAME original Q. -/
def compareOld : evaluation F j ⟶ toOldPresentation F j ⋙ JTSharedInsertionOldRaw.evaluation F j :=
  JTGraphCoveredLiftComparison.comparison Q (base F j)
    (collapsedFamily F j).labels (oldFamily F j).labels
    (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionOldGraph.oldTime F j)
    (JTSharedInsertionSeamNative.collapsedTarget F j) (JTSharedInsertionOldGraph.target F j)
    (projectionTarget F j) (JTSharedInsertionOldRaw.projectionTarget F j)
    (JTSharedInsertionPhaseGraph.collapsedTrace F j) (JTSharedInsertionOldGraph.parameter F j)
    (JTSharedInsertionNormalizedSeam.collapsedToOld F j) (toOld F j) (sourceChange F j)
    (sourceChange_cylinder F j) (native_equation F j) (coefficient_equation F j)
    (comparison_target F j) (target_raw F j) (old_target_raw F j)

/-- Forget the full collapsed presentation only to its actual triangle-choice index. -/
abbrev toChoices : BoundaryNecklaceComma.Presentation (reduced F j) ⥤ Index F j :=
  JTWhiskeredGraphEvaluation.toOriginal Q (collapsedFamily F j)
    (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
    (projectionTarget F j)

/-- The collapsed all-internal presentation is weak over NS.Index, for every target length. -/
theorem toChoices_weak : WeakEquivalence (nerveMap (toChoices F j)) := by
  apply JTWhiskeredGraphEvaluation.toOriginal_weak Q (collapsedFamily F j)
    (JTSharedInsertionPhaseGraph.oldTime F j) (JTSharedInsertionSeamNative.collapsedTarget F j)
    (projectionTarget F j)
  exact product_projection_trivial (codes (collapsedFamily F j).labels)
    (JTSharedInsertionPhaseGraph.oldTime F j) Q.code Q.map
    (JTSharedInsertionSeamNative.collapsedTarget F j)
    (JTSharedInsertionPhaseGraph.collapsedProjection F j)
    (JTSharedInsertionPhaseGraph.projection_trivialFibration F j
      (𝟙 (JTSharedInsertionPhaseGraph.collapsedCodes F j)))

end
end DaggerModels.PartII.JTSharedInsertionOldComparison
