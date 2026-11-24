import DaggerModelsPartII.JTFiniteCoefficientBridgeComparison
import DaggerModelsPartII.JTChangingFinalGraphComparison

/-!
# Comparing finitely many independent original final choices at once
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTFiniteFinalGraphComparison

open JTHigherInterleavedParameter (common)
open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgeVertexLift (sideVertical)
open JTFiniteCoefficientBridgeFamilies JTFiniteCoefficientBridgeComparison
open JTCommonCoefficientFinalFamilies JTCommonCoefficientFinalPullback
open JTCommonCoefficientFinalComma
open JTChangingFinalGraphComparison (FinalChoice)
open JTProjectiveOrderedFiberComparison JTNecklaceEndpointCylinder
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement MixedGraphCylinderTraversal
open JTHigherMixedGraphTargetLift (toNativeTarget)
open JTEndpointNormalizationLifts (identityFamily)
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {d : ℕ} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {q : (single d).toSSet ⟶ Raw W}
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)

private abbrev target :=
  (⟨single d, q, qx, qy⟩ : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
private abbrev D := JTTargetCommaPullback.diagram W x y (target qx qy)
private abbrev Fiber (n : SimplexCategory) :=
  CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under (code d)).obj n)
private abbrev Original :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) (target qx qy)

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
variable (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory)
variable (f : simplex b' ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable (F : ∀ e, FinalChoice qx qy (c e) n (SSet.stdSimplex.map (h e) ≫ f) s)

private theorem finalRow_eq (e : Fin (m + 1)) :
    SSet.stdSimplex.map (JTCommonCoefficientParameter.base (c e) n) ≫
        SSet.stdSimplex.map (h e) ≫ f = sideRow c u h hu n f e := by
  unfold sideRow
  rw [← Category.assoc, ← SSet.stdSimplex.map_comp, ← Category.assoc,
    ← SSet.stdSimplex.map_comp, side_base]

private def finalFunctor (e : Fin (m + 1)) : Fiber (d := d) n ⥤ Original qx qy :=
  finalComma n (JTMixedGraphOrderedLabel.orderedPoint (F e).families) (target qx qy) (F e).lift

private theorem exists_prescribed_side (e : Fin (m + 1)) :
    ∃ E : EdgeFamilies W ⦋d⦌ (common k n) (sideRow c u h hu n f e)
        (s ≫ J.map (sideSlice c n e)) x y,
      SSet.stdSimplex.map (sideVertical c n (graphIndex ⦋d⦌ k s 0) e) ≫ E.left =
        term (simplex n) ≫ vertexPoint W x ≫ identityFamily W ∧
      SSet.stdSimplex.map (sideVertical c n (graphIndex ⦋d⦌ k s (Fin.last d)) e) ≫ E.right =
        term (simplex n) ≫ vertexPoint W y ≫ identityFamily W ∧
      ∃ V : (under (code d)).obj n ⟶ (D qx qy).obj
          (prescribedIndex n (JTMixedGraphOrderedLabel.orderedPoint E)),
        V ≫ JTTargetCommaPullback.fst W x y (target qx qy)
          (prescribedIndex n (JTMixedGraphOrderedLabel.orderedPoint E)) =
          prescribedCylinder c n (nativeGraphParameter s)
            (JTMixedGraphOrderedLabel.orderedPoint E) e ∧
        V ≫ JTTargetCommaPullback.snd W x y (target qx qy)
          (prescribedIndex n (JTMixedGraphOrderedLabel.orderedPoint E)) = toNativeTarget d n ∧
        Nonempty (prescribedComma n (target qx qy) (JTMixedGraphOrderedLabel.orderedPoint E) V ⟶
          finalFunctor qx qy c h n f s F e) := by
  let C := F e
  let z := JTMixedGraphOrderedLabel.orderedPoint C.families
  obtain ⟨E, hE, hL, hR⟩ := exists_pulled_families (c e) n
    (SSet.stdSimplex.map (h e) ≫ f) s C.families
    (sideRow c u h hu n f e) (finalRow_eq c u h hu n f e) C.left_stationary C.right_stationary
  let V := JTCommonCoefficientFinalPullback.lift (c e) n z (nativeGraphParameter s)
    (target qx qy) C.lift C.decorated
  have H (w : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).obj
      (op (common k n))) (hw : w = JTCommonCoefficientParameter.pulledLabel W x y
      (code d) (c e) n z) :
      ∃ U : (under (code d)).obj n ⟶ (D qx qy).obj (prescribedIndex n w),
        U ≫ JTTargetCommaPullback.fst W x y (target qx qy) (prescribedIndex n w) =
          prescribedCylinder c n (nativeGraphParameter s) w e ∧
        U ≫ JTTargetCommaPullback.snd W x y (target qx qy) (prescribedIndex n w) =
          toNativeTarget d n ∧
        Nonempty (prescribedComma n (target qx qy) w U ⟶ finalFunctor qx qy c h n f s F e) := by
    subst w
    refine ⟨V, lift_fst _ _ _ _ _ _ _, ?_, ?_⟩
    · exact (lift_snd _ _ _ _ _ _ _).trans C.native
    · exact ⟨JTCommonCoefficientFinalComma.compareComma (c e) n z (nativeGraphParameter s)
        (target qx qy) C.lift C.decorated⟩
  exact ⟨E, hL, hR, H _ hE⟩

include hu in
/-- A single comparison in the original target comma compares all
independent final choices through their actual pulled comparisons. -/
theorem exists_compare_final_choices
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map u ≫ f) s = q) :
    ∃ (B : Fiber (d := d) (time m n) ⥤ Original qx qy)
      (G : Fin (m + 1) → Fiber (d := d) n ⥤ Original qx qy),
      ∀ e, Nonempty (G e ⟶ finalFunctor qx qy c h n f s F e) ∧
        Nonempty (G e ⟶ CostructuredArrow.map ((under (code d)).map (timeSide n e)) ⋙ B) := by
  classical
  choose E hL hR V hV hN hF using exists_prescribed_side qx qy c u h hu n f s F
  obtain ⟨B, hB⟩ := exists_compare_prescribed c u h hu n f s qx qy E V hW hq hL hR hV hN
  exact ⟨B, fun e ↦ prescribedComma n (target qx qy)
      (JTMixedGraphOrderedLabel.orderedPoint (E e)) (V e), fun e ↦ ⟨hF e, hB e⟩⟩

end

end DaggerModels.PartII.JTFiniteFinalGraphComparison
