import DaggerModelsPartII.JTChangingCoefficientBridgeComparison
import DaggerModelsPartII.JTCommonCoefficientFinalFamilies

/-!
# The comparison of the original final choices over composable graph operators
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTChangingFinalGraphComparison

open JTHigherInterleavedParameter (common ret)
open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgeFamilies
open JTChangingCoefficientBridgeComparison
open JTChangingCoefficientBridgeLift (sideVertical)
open JTChangingCoefficientBridgeCylinder (sideCylinderMap)
open JTCommonCoefficientFinalFamilies
open JTCommonCoefficientFinalPullback JTCommonCoefficientFinalComma
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

set_option maxHeartbeats 1000000 in
/-- A complete stationary final label and its original comparison to the
specified native target. -/
structure FinalChoice {k b : SimplexCategory} (u : k ⟶ b) (n : SimplexCategory)
    (f : simplex b ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k) where
  families : EdgeFamilies W ⦋d⦌ (common b n) (SSet.stdSimplex.map (ret b n) ≫ f)
    ((s ≫ J.map u) ≫ J.map (JTHigherInterleavedParameter.slice b n 0)) x y
  left_stationary : SSet.stdSimplex.map (JTHigherInterleavedParameter.vertical b n
      (graphIndex ⦋d⦌ b (s ≫ J.map u) 0)) ≫ families.left =
    term (simplex n) ≫ vertexPoint W x ≫ identityFamily W
  right_stationary : SSet.stdSimplex.map (JTHigherInterleavedParameter.vertical b n
      (graphIndex ⦋d⦌ b (s ≫ J.map u) (Fin.last d))) ≫ families.right =
    term (simplex n) ≫ vertexPoint W y ≫ identityFamily W
  lift : (under (code d)).obj n ⟶
    (D qx qy).obj (finalIndex n (JTMixedGraphOrderedLabel.orderedPoint families))
  decorated : lift ≫ JTTargetCommaPullback.fst W x y (target qx qy)
      (finalIndex n (JTMixedGraphOrderedLabel.orderedPoint families)) =
    finalCylinder u n (JTMixedGraphOrderedLabel.orderedPoint families) (nativeGraphParameter s)
  native : lift ≫ JTTargetCommaPullback.snd W x y (target qx qy)
      (finalIndex n (JTMixedGraphOrderedLabel.orderedPoint families)) = toNativeTarget d n

variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
variable (f : simplex b' ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)

private abbrev finalDegree (e : Fin 2) : SimplexCategory := if e = 0 then b else b'

private def finalOp (e : Fin 2) : k ⟶ finalDegree (b := b) (b' := b') e :=
  if he : e = 0 then by simpa only [finalDegree, he, if_true] using c
  else by simpa only [finalDegree, he, if_false] using c ≫ h

private def finalRow (e : Fin 2) : simplex (finalDegree (b := b) (b' := b') e) ⟶ row W ⦋d⦌ :=
  if he : e = 0 then by simpa only [finalDegree, he, if_true] using SSet.stdSimplex.map h ≫ f
  else by simpa only [finalDegree, he, if_false] using f

private theorem finalRow_eq (e : Fin 2) :
    SSet.stdSimplex.map (JTCommonCoefficientParameter.base (finalOp c h e) n) ≫ finalRow h f e =
      sideRow c h n f e := by
  fin_cases e
  · change SSet.stdSimplex.map (JTCommonCoefficientParameter.base c n) ≫ SSet.stdSimplex.map h ≫ f =
      SSet.stdSimplex.map (side c h n 0) ≫ SSet.stdSimplex.map (base c h n) ≫ f
    rw [← Category.assoc, ← SSet.stdSimplex.map_comp, ← Category.assoc,
      ← SSet.stdSimplex.map_comp, side_base_zero]
  · change SSet.stdSimplex.map (JTCommonCoefficientParameter.base (c ≫ h) n) ≫ f =
      SSet.stdSimplex.map (side c h n 1) ≫ SSet.stdSimplex.map (base c h n) ≫ f
    rw [← Category.assoc, ← SSet.stdSimplex.map_comp, side_base_one]

private theorem finalSlice_eq (e : Fin 2) :
    JTCommonCoefficientParameter.slice (finalOp c h e) n 0 = sideSlice c h n e := by
  fin_cases e <;> rfl

private theorem finalVertical_eq (e : Fin 2) (a : Fin (k.len + 1)) :
    JTCommonCoefficientParameter.vertical (finalOp c h e) n a = sideVertical c h n a e := by
  fin_cases e <;> rfl

variable (A : FinalChoice qx qy c n (SSet.stdSimplex.map h ≫ f) s)
variable (B : FinalChoice qx qy (c ≫ h) n f s)

private def finalChoice (e : Fin 2) :
    FinalChoice qx qy (finalOp c h e) n (finalRow h f e) s := by
  by_cases he : e = 0
  · subst e
    exact A
  · have he' : e = 1 := by omega
    subst e
    exact B

private abbrev z (e : Fin 2) := JTMixedGraphOrderedLabel.orderedPoint
  (finalChoice qx qy c h n f s A B e).families

private def finalFunctor (e : Fin 2) : Fiber (d := d) n ⥤ Original qx qy :=
  finalComma n (z qx qy c h n f s A B e) (target qx qy)
    (finalChoice qx qy c h n f s A B e).lift

private theorem sourceCylinder_eq (e : Fin 2)
    (v : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).obj
      (op (common (finalDegree (b := b) (b' := b') e) n))) :
    sourceCylinder (finalOp c h e) n v (nativeGraphParameter s) =
      prescribedCylinder c h n (nativeGraphParameter s)
        (JTCommonCoefficientParameter.pulledLabel W x y (code d) (finalOp c h e) n v) e := by
  apply Under.UnderMorphism.ext
  fin_cases e <;> rfl

private theorem exists_prescribed_side (e : Fin 2) :
    ∃ E : EdgeFamilies W ⦋d⦌ (common k n) (sideRow c h n f e)
        (s ≫ J.map (sideSlice c h n e)) x y,
      SSet.stdSimplex.map (sideVertical c h n (graphIndex ⦋d⦌ k s 0) e) ≫ E.left =
        term (simplex n) ≫ vertexPoint W x ≫ identityFamily W ∧
      SSet.stdSimplex.map (sideVertical c h n (graphIndex ⦋d⦌ k s (Fin.last d)) e) ≫ E.right =
        term (simplex n) ≫ vertexPoint W y ≫ identityFamily W ∧
      ∃ V : (under (code d)).obj n ⟶ (D qx qy).obj
          (prescribedIndex n (JTMixedGraphOrderedLabel.orderedPoint E)),
        V ≫ JTTargetCommaPullback.fst W x y (target qx qy)
          (prescribedIndex n (JTMixedGraphOrderedLabel.orderedPoint E)) =
          prescribedCylinder c h n (nativeGraphParameter s) (JTMixedGraphOrderedLabel.orderedPoint E) e ∧
        V ≫ JTTargetCommaPullback.snd W x y (target qx qy)
          (prescribedIndex n (JTMixedGraphOrderedLabel.orderedPoint E)) = toNativeTarget d n ∧
        Nonempty (prescribedComma n (target qx qy) (JTMixedGraphOrderedLabel.orderedPoint E) V ⟶
          finalFunctor qx qy c h n f s A B e) := by
  let C := finalChoice qx qy c h n f s A B e
  let v := z qx qy c h n f s A B e
  obtain ⟨E, hE, hL, hR⟩ := exists_pulled_families (finalOp c h e) n (finalRow h f e) s C.families
    (sideRow c h n f e) (finalRow_eq c h n f e) C.left_stationary C.right_stationary
  rw [finalVertical_eq c h n e] at hL hR
  let V := JTCommonCoefficientFinalPullback.lift (finalOp c h e) n v (nativeGraphParameter s)
    (target qx qy) C.lift C.decorated
  have H (w : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).obj
      (op (common k n))) (hw : w = JTCommonCoefficientParameter.pulledLabel W x y
      (code d) (finalOp c h e) n v) :
      ∃ U : (under (code d)).obj n ⟶ (D qx qy).obj (prescribedIndex n w),
        U ≫ JTTargetCommaPullback.fst W x y (target qx qy) (prescribedIndex n w) =
          prescribedCylinder c h n (nativeGraphParameter s) w e ∧
        U ≫ JTTargetCommaPullback.snd W x y (target qx qy) (prescribedIndex n w) =
          toNativeTarget d n ∧
        Nonempty (prescribedComma n (target qx qy) w U ⟶ finalFunctor qx qy c h n f s A B e) := by
    subst w
    refine ⟨V, ?_, ?_, ?_⟩
    · exact (lift_fst _ _ _ _ _ _ _).trans (sourceCylinder_eq c h n s e v)
    · exact (lift_snd _ _ _ _ _ _ _).trans C.native
    · exact ⟨compareComma (finalOp c h e) n v (nativeGraphParameter s)
        (target qx qy) C.lift C.decorated⟩
  have aux {a : k ⟶ common k n} (ha : JTCommonCoefficientParameter.slice (finalOp c h e) n 0 = a)
      (E : EdgeFamilies W ⦋d⦌ (common k n) (sideRow c h n f e)
        (s ≫ J.map (JTCommonCoefficientParameter.slice (finalOp c h e) n 0)) x y) :
      ∃ E' : EdgeFamilies W ⦋d⦌ (common k n) (sideRow c h n f e) (s ≫ J.map a) x y,
        E'.left = E.left ∧ E'.right = E.right ∧
        JTMixedGraphOrderedLabel.orderedPoint E' = JTMixedGraphOrderedLabel.orderedPoint E := by
    subst a
    exact ⟨E, rfl, rfl, rfl⟩
  obtain ⟨E', hL', hR', hz⟩ := aux (finalSlice_eq c h n e) E
  refine ⟨E', ?_, ?_, H _ (hz.trans hE)⟩
  · rwa [hL']
  · rwa [hR']

/-- The two independently prescribed original final comparisons of a
composable pair of graph operators lie in the same actual target-comma
component, for arbitrary internal necklaces on the two sides. -/
theorem final_zigzag
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map (c ≫ h) ≫ f) s = q)
    (P P' : Fiber (d := d) n) :
    Relation.EqvGen (fun I I' : Original qx qy ↦ Nonempty (I ⟶ I'))
      ((finalComma n (JTMixedGraphOrderedLabel.orderedPoint A.families)
        (target qx qy) A.lift).obj P)
      ((finalComma n (JTMixedGraphOrderedLabel.orderedPoint B.families)
        (target qx qy) B.lift).obj P') := by
  classical
  choose E hL hR V hV hN hF using exists_prescribed_side qx qy c h n f s A B
  obtain ⟨_, _, hZ⟩ := exists_compare_prescribed c h n f s qx qy E V hW hq hL hR hV hN
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨(hF 0).some.app P⟩))
    (Relation.EqvGen.trans _ _ _ (hZ P P') (Relation.EqvGen.rel _ _ ⟨(hF 1).some.app P'⟩))

end

end DaggerModels.PartII.JTChangingFinalGraphComparison
