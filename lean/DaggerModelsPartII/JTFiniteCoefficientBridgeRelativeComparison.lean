import DaggerModelsPartII.JTFiniteCoefficientBridgeRelativeRaw
import DaggerModelsPartII.JTFiniteCoefficientBridgeFaceReindex
import DaggerModelsPartII.JTFiniteCoefficientBridgeSubcollectionComma

/-!
# Comparing all prescribed lifts on overlapping subcollections at once
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe w

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeRelativeComparison

open JTFiniteCoefficientBridgeOrder (base bridge)
open JTFiniteCoefficientBridgeTime (time)
open JTFiniteCoefficientBridgePrism (vertical slice)
open JTFiniteCoefficientBridgeCopyFace
open JTFiniteCoefficientBridgeFaceReindex
open JTFiniteCoefficientBridgeRelativeRaw
open JTFiniteCoefficientBridgePullback (bridgeIndex bridgeCylinder joinedComma)
open JTFiniteCoefficientBridgeSubcollectionComma (compareJoinedComma)
open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts JTMixedGraphEdgeFamilyReindex
open JTMixedGraphRawRefinement MixedGraphCylinderTraversal
open JTChangingCoefficientBridgeFamilies
  (leftBase rightBase identityAt leftBase_precomp rightBase_precomp)
open JTNecklaceEndpointCylinder
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open JTHigherMixedGraphTargetLift (toNativeTarget toNativeTarget_natural)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (n : SimplexCategory) := SSet.stdSimplex.{0}.obj n
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
variable (f : Δ b' ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
variable {ι : Type w} (S : ι → Finset (Fin (m + 1))) (hS : ∀ e, (S e).Nonempty)

private abbrev small (e : ι) := smallCoefficients c (S e) (hS e)
private abbrev smallTime (e : ι) := time (smallDegree (S e)).len n
private abbrev smallBridge (e : ι) := bridge k n (smallDegree (S e)).len

/-- A prescribed actual triple of row maps on the smaller original parameter. -/
abbrev SmallerFamilies (e : ι) :=
  EdgeFamilies W ⦋d⦌ (smallBridge (k := k) n S e)
    (SSet.stdSimplex.map (base (small c S hS e) u n) ≫ f)
    (s ≫ J.map (slice (small c S hS e) u n 0)) x y

variable (E : ∀ e, SmallerFamilies (x := x) (y := y) c u n f s S hS e)

/-- Compatibility on a pair of actual coefficient face subcomplexes. -/
abbrev Compatible (G : ∀ e, (copyFace.{0} c u n (S e)).toSSet ⟶ row W ⦋1⦌) :=
  ∀ e e', SSet.Subcomplex.homOfLE (inf_le_left :
      copyFace.{0} c u n (S e) ⊓ copyFace c u n (S e') ≤ copyFace c u n (S e)) ≫ G e =
    SSet.Subcomplex.homOfLE (inf_le_right :
      copyFace.{0} c u n (S e) ⊓ copyFace c u n (S e') ≤ copyFace c u n (S e')) ≫ G e'

private abbrev leftFace (e : ι) := faceMap c u n (S e) (hS e) (E e).left
private abbrev rightFace (e : ι) := faceMap c u n (S e) (hS e) (E e).right
private abbrev label (e : ι) := JTMixedGraphOrderedLabel.orderedPoint (E e)
private abbrev Labels :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))

private theorem label_restriction
    (B : EdgeFamilies W ⦋d⦌ (bridge k n m) (SSet.stdSimplex.map (base c u n) ≫ f)
      (s ≫ J.map (slice c u n 0)) x y)
    (e : ι) (hL : (copyFace.{0} c u n (S e)).ι ≫ B.left = leftFace c u n f s S hS E e)
    (hR : (copyFace.{0} c u n (S e)).ι ≫ B.right = rightFace c u n f s S hS E e) :
    (Labels (W := W) (x := x) (y := y) (d := d)).map (smallOperator c u n (S e) (hS e)).op
      (JTMixedGraphOrderedLabel.orderedPoint B) = label c u n f s S hS E e := by
  have L : SSet.stdSimplex.map (smallOperator c u n (S e) (hS e)) ≫ B.left =
      (E e).left := by
    simpa only [leftFace, coefficientIso_ι_assoc, coefficientIso_faceMap] using
      congrArg (fun v ↦ (coefficientIso.{0} c u n (S e) (hS e)).hom ≫ v) hL
  have R : SSet.stdSimplex.map (smallOperator c u n (S e) (hS e)) ≫ B.right =
      (E e).right := by
    simpa only [rightFace, coefficientIso_ι_assoc, coefficientIso_faceMap] using
      congrArg (fun v ↦ (coefficientIso.{0} c u n (S e) (hS e)).hom ≫ v) hR
  symm
  apply orderedPoint_reindex_of_rows (smallOperator c u n (S e) (hS e))
    (JTMixedGraphOrderedLabel.families B) (JTMixedGraphOrderedLabel.families (E e))
  · dsimp only [JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc, L]
  · dsimp only [JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc (SSet.stdSimplex.map (smallOperator c u n (S e) (hS e))),
      ← Category.assoc (SSet.stdSimplex.map (smallOperator c u n (S e) (hS e))),
      ← SSet.stdSimplex.map_comp, smallOperator_base]
  · dsimp only [JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc, R]

private abbrev D (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  JTTargetCommaPullback.diagram W x y Q
private abbrev Original (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q
private abbrev Fiber (d : ℕ) (n : SimplexCategory) :=
  CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under (code d)).obj n)

private theorem compare_one
    (I : Finset (Fin (m + 1))) (hI : I.Nonempty)
    (z : (Labels (W := W) (x := x) (y := y) (d := d)).obj (op (bridge k n m)))
    (w : (Labels (W := W) (x := x) (y := y) (d := d)).obj (op (bridge k n (smallDegree I).len)))
    (hw : w = (Labels (W := W) (x := x) (y := y) (d := d)).map
      (smallOperator c u n I hI).op z)
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (V : (under (code d)).obj (time (smallDegree I).len n) ⟶ (D Q).obj (bridgeIndex n w))
    (U : (under (code d)).obj (time m n) ⟶ (D Q).obj (bridgeIndex n z))
    (hV : V ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n w) =
      bridgeCylinder (smallCoefficients c I hI) u n w (nativeGraphParameter s))
    (hU : U ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
      bridgeCylinder c u n z (nativeGraphParameter s))
    (hN : V ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n w) =
      (under (code d)).map (smallTimeOperator n I hI) ≫
        U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z)) :
    Nonempty (joinedComma n w Q V ⟶
      CostructuredArrow.map ((under (code d)).map (smallTimeOperator n I hI)) ⋙
        joinedComma n z Q U) := by
  subst w
  exact ⟨compareJoinedComma (smallCoefficients c I hI) c u n (copyInclusion I hI)
    (JTHigherInterleavedParameter.timeInclusion_injective I hI)
    (smallCoefficient_agrees c n I hI) z (nativeGraphParameter s) Q V U hV hU hN⟩

set_option maxHeartbeats 1000000 in
/-- The independently prescribed comparisons on overlapping subcollections
all compare naturally to one lift in the original target comma. -/
theorem exists_compare_of_faces [Fintype ι]
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    {q : (single d).toSSet ⟶ Raw W}
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map u ≫ f) s = q)
    (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
    (hL : ∀ e, SSet.stdSimplex.map (vertical (small c S hS e) u n
        (graphIndex ⦋d⦌ k s 0)) ≫ (E e).left =
      term (Δ (smallTime n S e)) ≫ identityAt x)
    (hR : ∀ e, SSet.stdSimplex.map (vertical (small c S hS e) u n
        (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ (E e).right =
      term (Δ (smallTime n S e)) ≫ identityAt y)
    (hLC : Compatible c u n S (leftFace c u n f s S hS E))
    (hRC : Compatible c u n S (rightFace c u n f s S hS E)) :
    let Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y) := ⟨single d, q, qx, qy⟩
    ∀ (V : ∀ e, (under (code d)).obj (smallTime n S e) ⟶
        (D Q).obj (bridgeIndex n (label c u n f s S hS E e))),
      (∀ e, V e ≫ JTTargetCommaPullback.fst W x y Q
          (bridgeIndex n (label c u n f s S hS E e)) =
        bridgeCylinder (small c S hS e) u n (label c u n f s S hS E e)
          (nativeGraphParameter s)) →
      (∀ e, V e ≫ JTTargetCommaPullback.snd W x y Q
          (bridgeIndex n (label c u n f s S hS E e)) =
        toNativeTarget d (smallTime n S e)) →
      ∃ F : Fiber d (time m n) ⥤ Original Q, ∀ e,
        Nonempty (joinedComma n (label c u n f s S hS E e) Q (V e) ⟶
          CostructuredArrow.map ((under (code d)).map (smallTimeOperator n (S e) (hS e))) ⋙ F) := by
  intro Q V hV hN
  let L : EndpointFaces c u n S (graphIndex ⦋d⦌ k s 0) (leftBase f x) (identityAt x) :=
    { map := leftFace c u n f s S hS E
      base_eq := fun e ↦ faceMap_base c u n (S e) (hS e) (leftBase f x) (E e).left
        ((E e).left_boundary.trans (leftBase_precomp (base (small c S hS e) u n) f x).symm)
      stationary := fun e ↦ faceMap_stationary_of_vertical c u n (S e) (hS e) _
        (identityAt x) (E e).left (hL e)
      overlap := hLC }
  let R : EndpointFaces c u n S (graphIndex ⦋d⦌ k s (Fin.last d)) (rightBase f y) (identityAt y) :=
    { map := rightFace c u n f s S hS E
      base_eq := fun e ↦ faceMap_base c u n (S e) (hS e) (rightBase f y) (E e).right
        ((E e).right_boundary.trans (rightBase_precomp (base (small c S hS e) u n) f y).symm)
      stationary := fun e ↦ faceMap_stationary_of_vertical c u n (S e) (hS e) _
        (identityAt y) (E e).right (hR e)
      overlap := hRC }
  obtain ⟨B, hB₀, hB₁, U, hU, hUN⟩ :=
    exists_lift_over_raw_of_faces c u n S f s L R hW hq qx qy
  let z := JTMixedGraphOrderedLabel.orderedPoint B
  refine ⟨joinedComma n z Q U, fun e ↦ ?_⟩
  refine compare_one c u n s (S e) (hS e) z _
    (label_restriction c u n f s S hS E B e (hB₀ e) (hB₁ e)).symm
    Q (V e) U (hV e) hU ?_
  exact (hN e).trans
    ((toNativeTarget_natural d (smallTimeOperator n (S e) (hS e))).symm.trans
      (congrArg (fun v ↦ (under (code d)).map (smallTimeOperator n (S e) (hS e)) ≫ v)
        hUN.symm))

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeRelativeComparison
