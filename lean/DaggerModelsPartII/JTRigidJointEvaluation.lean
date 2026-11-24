import DaggerModelsPartII.JTRigidWholeGraphCover
import DaggerModelsPartII.JTFullBoundaryGraphEvaluation

/-! Evaluation of the entire rigid joint cover in the original fixed-target comma. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRigidJointEvaluation

open JTJointRelativeGraphFamily (RawOn native coefficient leftLeg rightLeg originalParameter
  originalLeft originalRight)
open JTJointRelativeParameters (withTime withTimeMap underlying_isPushout)
open JTParametrizedTargetFamilies (Family)
open JTTargetIntervalOverMapping (left right overlapToLeft overlapToRight)
open JTTargetJointMarks (Joint)
open JTRigidJointGraphCover (overlapData)
open JTRigidOverlapDiagram (PairwiseFiberAgreement Data CrossAgreement)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj zero
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)

private abbrev π := JTRigidWholeGraphCover.projection F j s t
private abbrev θ := JTRigidWholeGraphCover.parameter F j s t

/-- The entire covered source after collapsing both full inverse-image endpoint lines. -/
abbrev reduced := JTFullBoundaryGraphEvaluation.reduced F (π F j s t)

abbrev Presentation := BoundaryNecklaceComma.Presentation (reduced F j s t)

/-- Use the actual fixed-target maps of the two references to evaluate the glued data. -/
def evaluate (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t) :
    Presentation F j s t ⥤ JTGraphFactoredPresentation.TargetComma Q :=
  JTFullBoundaryGraphEvaluation.evaluate F (π F j s t) (θ F j s t)
    (JTRigidWholeGraphCover.rawOn F j s t hs ht)

/-- Every old internal-necklace fiber is retained up to weak equivalence. -/
theorem presentationProjection_weak (h : PairwiseFiberAgreement (overlapData F j s t)) :
    WeakEquivalence (nerveMap (JTFullBoundaryGraphEvaluation.presentationProjection F
      (π F j s t))) :=
  JTFullBoundaryGraphEvaluation.presentationProjection_weak F (π F j s t)
    (JTRigidWholeGraphCover.projection_trivialFibration F j s t h)

/-- The rigid cover retains the weak type of the entire original index. -/
theorem forget_weak (h : PairwiseFiberAgreement (overlapData F j s t)) :
    WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F j s t)))) :=
  JTFullBoundaryGraphEvaluation.forget_weak F (π F j s t)
    (JTRigidWholeGraphCover.projection_trivialFibration F j s t h)

/-- A weakly contractible coherent index gives a weakly contractible full evaluation domain. -/
theorem presentation_point_GW (h : PairwiseFiberAgreement (overlapData F j s t))
    (hI : GW (pointMap (nerve I))) : GW (pointMap (nerve (Presentation F j s t))) := by
  let p := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F j s t))
  letI : WeakEquivalence (nerveMap p) := forget_weak F j s t h
  letI : WeakEquivalence (pointMap (nerve I)) := (weakEquivalence_iff_GW _).mpr hI
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (nerveMap p ≫ pointMap _) (pointMap _)]
  infer_instance

private theorem cross_of_reference_eq (D : Data I)
    (h : D.leftInclusion ≫ D.leftReference = D.rightInclusion ≫ D.rightReference) :
    CrossAgreement D := by
  intro p u _ _
  have ht := congrFun (NatTrans.congr_app (NatTrans.congr_app h p) zero) u
  exact congrArg (fun a ↦ JTCodiscreteParameterPairing.coord (D.degree.obj p) zero a 0) ht

set_option maxHeartbeats 750000 in
/-- Restrictions of the original coherent family satisfy the exact joint test. -/
theorem original_pairwise :
    PairwiseFiberAgreement (overlapData F j (originalLeft F j) (originalRight F j)) := by
  apply (JTRigidOverlapDiagram.pairwise_iff_commonCover _).mpr
  apply JTRigidOverlapDiagram.commonCover_of_crossAgreement
  apply cross_of_reference_eq
  change withTimeMap Q.map J time (native F) (overlapToLeft Q.code j) ≫
      (leftLeg F j ≫ originalParameter F) =
    withTimeMap Q.map J time (native F) (overlapToRight Q.code j) ≫
      (rightLeg F j ≫ originalParameter F)
  simp only [← Category.assoc]
  exact congrArg (· ≫ originalParameter F) (underlying_isPushout Q J time (native F) j).w

section OriginalComparison

open CartesianMonoidalCategory
open JTParametrizedTargetFamilies (codes)
open JTNecklaceEndpointCylinder (cylinder)
open JTJointRelativeGraphFamily (original_rawOn)

private abbrev oldLeft := originalLeft F j
private abbrev oldRight := originalRight F j

set_option maxHeartbeats 700000 in
/-- The covered evaluation from the original restrictions compares naturally
to the original parametrized evaluation on every projected necklace. -/
def compareOriginal :
    evaluate F j (oldLeft F j) (oldRight F j) (original_rawOn F (leftLeg F j))
        (original_rawOn F (rightLeg F j)) ⟶
      JTFullBoundaryGraphEvaluation.presentationProjection F
        (π F j (oldLeft F j) (oldRight F j)) ⋙ JTParametrizedTargetFamilies.evaluate F := by
  let s := oldLeft F j
  let t := oldRight F j
  let h := JTRigidWholeGraphCover.rawOn F j s t
    (original_rawOn F (leftLeg F j)) (original_rawOn F (rightLeg F j))
  apply JTFullBoundaryGraphEvaluation.compareOriginal F (π F j s t) (θ F j s t) h
  intro p
  let T := (codes L).obj p
  let k := (coefficient (L := L)).obj p
  let n := time.obj p
  let axis := fst T.toSSet (J.obj n)
  change lift ((π F j s t).app p ≫ axis) ((θ F j s t).app p) ≫ (cylinder T).app k =
    (π F j s t).app p ≫ (cylinder T).app n ≫
      JTInterpolatedReducedCylinder.cylinderMap T (F.parameter p)
  rw [JTInterpolatedReducedCylinder.cylinderMap_cylinder]
  exact JTRigidWholeGraphCover.originalGraph F j p

end OriginalComparison

end

end DaggerModels.PartII.JTRigidJointEvaluation
