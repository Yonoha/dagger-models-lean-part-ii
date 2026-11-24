import DaggerModelsPartII.JTRigidOverlapDiagram
import DaggerModelsPartII.JTGraphParameterSourceRestriction
import DaggerModelsPartII.JTRigidJointEvaluation

/-!
# Rigid overlap tests from a common reference graph

The common coefficient is taken at the original vertex and transported
along each outgoing operator. Exact side graph equations supply the rigid
vertex agreements used in those transports.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTRigidOverlapDiagram

private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev J := GroupoidSimplex.parameter

noncomputable section

variable {I : Type} [SmallCategory I] (D : Data I)

private abbrev commonValue (base : D.overlap ⟶ D.degree ⋙ J)
    (p : I) (u : (D.overlap.obj p).obj zero) :
    Fin ((D.degree.obj p).len + 1) :=
  JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
    ((base.app p).app zero u) 0

private theorem commonValue_natural (base : D.overlap ⟶ D.degree ⋙ J)
    {p q : I} (a : p ⟶ q) (u : (D.overlap.obj p).obj zero) :
    commonValue D base q (moved D a u) =
      coefficientMap D a (commonValue D base p u) := by
  have hn := congrFun (NatTrans.congr_app (base.naturality a) zero) u
  change (base.app q).app zero (moved D a u) =
    (J.map (D.degree.map a)).app zero ((base.app p).app zero u) at hn
  change JTCodiscreteParameterPairing.coord (D.degree.obj q) zero
    ((base.app q).app zero (moved D a u)) 0 = _
  rw [hn, JTCodiscreteParameterPairing.coord_map]

/-- Rigid agreement with a natural common trace supplies the simultaneous
    coefficient for each pair of downstream tests. -/
theorem pairwise_of_common_rigid_values (base : D.overlap ⟶ D.degree ⋙ J)
    (hL : ∀ p u,
      JTGraphParameterSourceRestriction.RigidVertex (D.leftCode p) (D.leftNative p)
        (leftImage D p u) → leftValue D p u = commonValue D base p u)
    (hR : ∀ p u,
      JTGraphParameterSourceRestriction.RigidVertex (D.rightCode p) (D.rightNative p)
        (rightImage D p u) → rightValue D p u = commonValue D base p u) :
    PairwiseFiberAgreement D := by
  intro p u l r
  rcases l with ⟨⟨q, a⟩, hl⟩
  rcases r with ⟨⟨q', b⟩, hr⟩
  refine ⟨commonValue D base p u, ?_, ?_⟩
  · change coefficientMap D a (commonValue D base p u) =
      leftValue D q (moved D a u)
    rw [← commonValue_natural D base a u]
    exact (hL q (moved D a u) hl).symm
  · change coefficientMap D b (commonValue D base p u) =
      rightValue D q' (moved D b u)
    rw [← commonValue_natural D base b u]
    exact (hR q' (moved D b u) hr).symm

private theorem rigid_coord_eq_of_graph {X : SSet.{0}} (T : NecklaceCode)
    (k : SimplexCategory) (f : X ⟶ T.toSSet) (s t : X ⟶ J.obj k)
    (h : lift f s ≫ (JTNecklaceEndpointCylinder.cylinder T).app k =
      lift f t ≫ (JTNecklaceEndpointCylinder.cylinder T).app k)
    (x : X.obj zero) (hx : JTGraphParameterSourceRestriction.RigidVertex T f x) :
    JTCodiscreteParameterPairing.coord k zero (s.app zero x) 0 =
      JTCodiscreteParameterPairing.coord k zero (t.app zero x) 0 := by
  obtain ⟨d, z, v, hn, hv⟩ := hx
  have he := JTGraphParameterSourceRestriction.exact_parameter_eq_at_incident_vertex
    T k f s t h d z hn v
  have he' := congrArg SSet.yonedaEquiv he
  have he'' : s.app zero x = t.app zero x := by
    have ht : s.app zero (SSet.yonedaEquiv (v ≫ z)) =
        t.app zero (SSet.yonedaEquiv (v ≫ z)) := by
      simpa only [Category.assoc, SSet.yonedaEquiv_comp] using he'
    simpa only [hv] using ht
  exact congrArg (fun a ↦ JTCodiscreteParameterPairing.coord k zero a 0) he''

/-- Exact equality of both complete side graphs with compatible baseline graphs
    supplies every cross-side downstream fiber test. -/
theorem pairwise_of_common_exact_graphs
    (baseL : D.left ⟶ D.degree ⋙ J) (baseR : D.right ⟶ D.degree ⋙ J)
    (hbase : D.leftInclusion ≫ baseL = D.rightInclusion ≫ baseR)
    (hgraphL : ∀ p,
      lift (D.leftNative p) (D.leftReference.app p) ≫
          (JTNecklaceEndpointCylinder.cylinder (D.leftCode p)).app (D.degree.obj p) =
        lift (D.leftNative p) (baseL.app p) ≫
          (JTNecklaceEndpointCylinder.cylinder (D.leftCode p)).app (D.degree.obj p))
    (hgraphR : ∀ p,
      lift (D.rightNative p) (D.rightReference.app p) ≫
          (JTNecklaceEndpointCylinder.cylinder (D.rightCode p)).app (D.degree.obj p) =
        lift (D.rightNative p) (baseR.app p) ≫
          (JTNecklaceEndpointCylinder.cylinder (D.rightCode p)).app (D.degree.obj p)) :
    PairwiseFiberAgreement D := by
  apply pairwise_of_common_rigid_values D (D.leftInclusion ≫ baseL)
  · intro p u hr
    have h := rigid_coord_eq_of_graph (D.leftCode p) (D.degree.obj p)
      (D.leftNative p) (D.leftReference.app p) (baseL.app p) (hgraphL p)
      (leftImage D p u) hr
    exact h
  · intro p u hr
    have h := rigid_coord_eq_of_graph (D.rightCode p) (D.degree.obj p)
      (D.rightNative p) (D.rightReference.app p) (baseR.app p) (hgraphR p)
      (rightImage D p u) hr
    have hb := congrFun (NatTrans.congr_app (NatTrans.congr_app hbase p) zero) u
    change (baseL.app p).app zero (leftImage D p u) =
      (baseR.app p).app zero (rightImage D p u) at hb
    change JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
      ((D.rightReference.app p).app zero (rightImage D p u)) 0 =
      JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
        ((baseL.app p).app zero (leftImage D p u)) 0
    exact h.trans (congrArg
      (fun a ↦ JTCodiscreteParameterPairing.coord (D.degree.obj p) zero a 0) hb.symm)

end
end DaggerModels.PartII.JTRigidOverlapDiagram

namespace DaggerModels.PartII.JTRigidJointGraphCover

private abbrev J := GroupoidSimplex.parameter

open JTJointRelativeGraphFamily (native coefficient leftLeg rightLeg originalParameter)
open JTJointRelativeParameters (withTime withTimeMap underlying_isPushout)
open JTParametrizedTargetFamilies (Family)
open JTTargetIntervalOverMapping (left right overlapToLeft overlapToRight)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶
    coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶
    coefficient (L := L) ⋙ J)

set_option maxHeartbeats 750000 in
theorem pairwise_of_exact_graphs
    (hL : ∀ p,
      lift ((overlapData F j s t).leftNative p) (s.app p) ≫
          (JTNecklaceEndpointCylinder.cylinder
            ((overlapData F j s t).leftCode p)).app
              ((overlapData F j s t).degree.obj p) =
        lift ((overlapData F j s t).leftNative p)
          ((leftLeg F j ≫ originalParameter F).app p) ≫
          (JTNecklaceEndpointCylinder.cylinder
            ((overlapData F j s t).leftCode p)).app
              ((overlapData F j s t).degree.obj p))
    (hR : ∀ p,
      lift ((overlapData F j s t).rightNative p) (t.app p) ≫
          (JTNecklaceEndpointCylinder.cylinder
            ((overlapData F j s t).rightCode p)).app
              ((overlapData F j s t).degree.obj p) =
        lift ((overlapData F j s t).rightNative p)
          ((rightLeg F j ≫ originalParameter F).app p) ≫
          (JTNecklaceEndpointCylinder.cylinder
            ((overlapData F j s t).rightCode p)).app
              ((overlapData F j s t).degree.obj p)) :
    JTRigidOverlapDiagram.PairwiseFiberAgreement (overlapData F j s t) := by
  apply JTRigidOverlapDiagram.pairwise_of_common_exact_graphs
    (overlapData F j s t) (leftLeg F j ≫ originalParameter F)
    (rightLeg F j ≫ originalParameter F)
  · change withTimeMap Q.map J time (native F) (overlapToLeft Q.code j) ≫
        (leftLeg F j ≫ originalParameter F) =
      withTimeMap Q.map J time (native F) (overlapToRight Q.code j) ≫
        (rightLeg F j ≫ originalParameter F)
    simp only [← Category.assoc]
    exact congrArg (· ≫ originalParameter F)
      (underlying_isPushout Q J time (native F) j).w
  · exact hL
  · exact hR

open JTJointRelativeGraphFamily (RawOn original_rawOn)
open JTParametrizedTargetFamilies (codes)
open JTNecklaceEndpointCylinder (cylinder)
open DecoratedCylinderNecklacePresentation (underCocone)

private abbrev axis (p : I) :=
  fst ((codes L).obj p).toSSet (J.obj (time.obj p))

private abbrev k (p : I) := (coefficient (L := L)).obj p
private abbrev T (p : I) := (codes L).obj p

private abbrev originalGraph (p : I) :=
  lift (axis (L := L) (time := time) p) (F.parameter p) ≫
    (cylinder (T (L := L) p)).app (k (L := L) p)

private abbrev sideGraph {Y : SSet.{0}} (p : I)
    (a : Y ⟶ _)
    (r : Y ⟶ J.obj (k (L := L) p)) :=
  lift (a ≫ axis (L := L) (time := time) p) r ≫
    (cylinder (T (L := L) p)).app (k (L := L) p)

private abbrev wholeSource := withTime Q.map J time (native F)
  (JTTargetIntervalOverMapping.whole Q.code)

private theorem raw_of_side_graph {Z : I ⥤ SSet.{0}}
    (a : Z ⟶ wholeSource F) (r : Z ⟶ coefficient (L := L) ⋙ J)
    (h : ∀ p, sideGraph (L := L) (time := time) p (a.app p) (r.app p) =
      a.app p ≫ originalGraph F p) :
    RawOn F a r := by
  intro p
  have h₁ := congrArg (· ≫ ((underCocone W x y).app (L.obj p)).right) (h p)
  have h₂ : lift (axis (L := L) (time := time) p)
      (F.parameter p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) ≫
        ((underCocone W x y).app (L.obj p)).right =
      axis (L := L) (time := time) p ≫ (F.collapse.app p).map ≫ Q.map := by
    have h₃ := original_rawOn F (𝟙 (wholeSource F)) p
    exact h₃
  simpa only [sideGraph, originalGraph, Category.assoc, h₂] using h₁

variable
  (hL : ∀ p, sideGraph (L := L) (time := time) p ((leftLeg F j).app p) (s.app p) =
    (leftLeg F j).app p ≫ originalGraph F p)
  (hR : ∀ p, sideGraph (L := L) (time := time) p ((rightLeg F j).app p) (t.app p) =
    (rightLeg F j).app p ≫ originalGraph F p)

private abbrev π := JTRigidWholeGraphCover.projection F j s t
private abbrev θ := JTRigidWholeGraphCover.parameter F j s t

set_option maxHeartbeats 700000 in
/-- Independent side parameters with the original graph image give a covered
evaluation comparing to the original parametrized evaluation. -/
def compareOriginalOfSideGraphs :
    JTRigidJointEvaluation.evaluate F j s t (raw_of_side_graph F (leftLeg F j) s hL)
        (raw_of_side_graph F (rightLeg F j) t hR) ⟶
      JTFullBoundaryGraphEvaluation.presentationProjection F (π F j s t) ⋙
        JTParametrizedTargetFamilies.evaluate F := by
  let raw := JTRigidWholeGraphCover.rawOn F j s t
    (raw_of_side_graph F (leftLeg F j) s hL) (raw_of_side_graph F (rightLeg F j) t hR)
  apply JTFullBoundaryGraphEvaluation.compareOriginal F (π F j s t) (θ F j s t) raw
  intro p
  change sideGraph (L := L) (time := time) p ((π F j s t).app p) ((θ F j s t).app p) =
    (π F j s t).app p ≫ (cylinder (T (L := L) p)).app (time.obj p) ≫
      JTInterpolatedReducedCylinder.cylinderMap (T (L := L) p) (F.parameter p)
  rw [JTInterpolatedReducedCylinder.cylinderMap_cylinder]
  have h := JTRigidWholeGraphCover.preservesImage F j s t p (𝟙 _) (originalGraph F p)
    (by simpa only [Category.comp_id] using hL p)
    (by simpa only [Category.comp_id] using hR p)
  simpa only [sideGraph, originalGraph, Category.comp_id] using h

open HomotopicalAlgebra in
open scoped SSet.modelCategoryQuillen in
include hL hR in
/-- The original graph image on both sides makes the comparison a weak cover
of the whole original internal-necklace presentation. -/
theorem presentationProjection_weak_of_side_graphs :
    WeakEquivalence (nerveMap
      (JTFullBoundaryGraphEvaluation.presentationProjection F (π F j s t))) := by
  apply JTRigidJointEvaluation.presentationProjection_weak F j s t
  apply pairwise_of_exact_graphs F j s t
  · intro p
    refine (hL p).trans ?_
    simp only [originalGraph, ← Category.assoc, comp_lift]
    rfl
  · intro p
    refine (hR p).trans ?_
    simp only [originalGraph, ← Category.assoc, comp_lift]
    rfl

end
end DaggerModels.PartII.JTRigidJointGraphCover
