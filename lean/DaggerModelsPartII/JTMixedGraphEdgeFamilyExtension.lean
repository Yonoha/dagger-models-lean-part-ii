import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex
import NativeCoherentCotensorResolutionWeak

/-!
# Extending chosen endpoint families across an injective parameter operator
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTMixedGraphEdgeFamilyExtension

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTMixedGraphEdgeFamilyReindex

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter

private theorem stdMap_weak {k l : SimplexCategory} (j : k ⟶ l) :
    WeakEquivalence (SSet.stdSimplex.{0}.map j) := by
  let t (a : SimplexCategory) := CartesianMonoidalCategory.toUnit (Δ a)
  have weak (a : SimplexCategory) : WeakEquivalence (t a) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerNativeCoherentCotensorResolutionWeak.simplex_parameter_GW a)
  haveI := weak k
  haveI := weak l
  exact weakEquivalence_of_postcomp_of_fac
    (show SSet.stdSimplex.map j ≫ t l = t k from
      CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _)

private theorem stdMap_cofibration {k l : SimplexCategory} (j : k ⟶ l) [Mono j] :
    Cofibration (SSet.stdSimplex.{0}.map j) := by
  apply (SSet.modelCategoryQuillen.cofibration_iff _).mpr
  rw [NatTrans.mono_iff_mono_app]
  intro a
  apply (mono_iff_injective _).mpr
  intro u v h
  apply SSet.stdSimplex.objEquiv.injective
  apply (cancel_mono j).mp
  exact congrArg SSet.stdSimplex.objEquiv h

variable {W : Source} {d : ℕ} {k l : SimplexCategory}
variable (j : k ⟶ l) (f : Δ l ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (e : EdgeFamilies W ⦋d⦌ k (SSet.stdSimplex.map j ≫ f) s x y)

private def constant (x : (row W ⦋0⦌).obj (op ⦋0⦌)) (a : SimplexCategory) :
    Δ a ⟶ row W ⦋0⦌ :=
  SSet.stdSimplex.isTerminalObj₀.from (Δ a) ≫ vertexPoint W x

private theorem constant_natural (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.stdSimplex.map j ≫ constant x l = constant x k := by
  unfold constant
  rw [← Category.assoc]
  congr 1

private def leftSquare :
    CommSq e.left (SSet.stdSimplex.map j) (endpointArrow W)
      (prod.lift (constant x l) (f ≫ rowVertex W ⦋d⦌ 0)) := by
  constructor
  rw [prod.comp_lift, constant_natural, ← Category.assoc]
  exact e.left_boundary

private def rightSquare :
    CommSq e.right (SSet.stdSimplex.map j) (endpointArrow W)
      (prod.lift (f ≫ rowVertex W ⦋d⦌ (Fin.last d)) (constant y l)) := by
  constructor
  rw [prod.comp_lift, constant_natural, ← Category.assoc]
  exact e.right_boundary

private theorem vertex_map (i : Fin (d + 1)) :
    vertex k (graphIndex ⦋d⦌ k s i) ≫ SSet.stdSimplex.map j =
      vertex l (graphIndex ⦋d⦌ l (s ≫ J.map j) i) := by
  rw [graphIndex_reindex]
  unfold vertex
  rw [← SSet.stdSimplex.{0}.map_comp, SimplexCategory.const_comp]

private theorem edgeFamilies_ext
    {a b : EdgeFamilies W ⦋d⦌ k (SSet.stdSimplex.map j ≫ f) s x y}
    (hl : a.left = b.left) (hr : a.right = b.right) : a = b := by
  cases a
  cases b
  cases hl
  cases hr
  rfl

set_option maxHeartbeats 800000 in
/-- An injective parameter operator admits an extension of both actual
endpoint families whose restriction is exactly the given pair. -/
theorem exists_extension (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
    IsFibrant W) [Mono j] :
    ∃ E : EdgeFamilies W ⦋d⦌ l f (s ≫ J.map j) x y, restrictEdgeFamilies j f s E = e := by
  haveI := stdMap_weak j
  haveI := stdMap_cofibration j
  haveI := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  let L := leftSquare j f s e
  let M := rightSquare j f s e
  let E : EdgeFamilies W ⦋d⦌ l f (s ≫ J.map j) x y :=
    { left := L.lift
      right := M.lift
      left_boundary := L.fac_right
      right_boundary := M.fac_right
      left_degenerate := by
        rw [← vertex_map j s 0, Category.assoc, L.fac_left]
        exact e.left_degenerate
      right_degenerate := by
        rw [← vertex_map j s (Fin.last ⦋d⦌.len), Category.assoc, M.fac_left]
        exact e.right_degenerate }
  exact ⟨E, edgeFamilies_ext j f s L.fac_left M.fac_left⟩

end

end DaggerModels.PartII.JTMixedGraphEdgeFamilyExtension
