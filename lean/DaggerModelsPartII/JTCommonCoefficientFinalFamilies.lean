import DaggerModelsPartII.JTCommonCoefficientFinalCylinder
import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex

/-!
# The original stationary endpoint families restrict from a final coefficient
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCommonCoefficientFinalFamilies

open JTHigherInterleavedParameter (common)
open JTCommonCoefficientParameter
open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts JTMixedGraphEdgeFamilyReindex
open JTEndpointNormalizationLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{0}.obj a
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {d : ℕ} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {k b : SimplexCategory} (u : k ⟶ b) (n : SimplexCategory)
variable (f : simplex b ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)

private theorem toFinal_row :
    SSet.stdSimplex.map (toFinal u n) ≫
      SSet.stdSimplex.map (JTHigherInterleavedParameter.ret b n) ≫ f =
    SSet.stdSimplex.map (base u n) ≫ f := by
  rw [← Category.assoc, ← SSet.stdSimplex.map_comp, toFinal_ret]

private theorem toFinal_graph :
    (s ≫ J.map (slice u n 0)) ≫ J.map (toFinal u n) =
      (s ≫ J.map u) ≫ J.map (JTHigherInterleavedParameter.slice b n 0) := by
  rw [Category.assoc, Category.assoc, ← J.map_comp, ← J.map_comp, slice_toFinal]

variable (E : EdgeFamilies W ⦋d⦌ (common b n)
  (SSet.stdSimplex.map (JTHigherInterleavedParameter.ret b n) ≫ f)
  ((s ≫ J.map u) ≫ J.map (JTHigherInterleavedParameter.slice b n 0)) x y)

/-- The pullback of an independently supplied final family has the exact
prescribed source coefficient and both complete stationary endpoint maps. -/
theorem exists_pulled_families
    (f₀ : simplex (common k n) ⟶ row W ⦋d⦌)
    (hf : SSet.stdSimplex.map (base u n) ≫ f = f₀)
    (hleft : SSet.stdSimplex.map (JTHigherInterleavedParameter.vertical b n
        (graphIndex ⦋d⦌ b (s ≫ J.map u) 0)) ≫ E.left =
      term (simplex n) ≫ vertexPoint W x ≫ identityFamily W)
    (hright : SSet.stdSimplex.map (JTHigherInterleavedParameter.vertical b n
        (graphIndex ⦋d⦌ b (s ≫ J.map u) (Fin.last d))) ≫ E.right =
      term (simplex n) ≫ vertexPoint W y ≫ identityFamily W) :
    ∃ F : EdgeFamilies W ⦋d⦌ (common k n) f₀ (s ≫ J.map (slice u n 0)) x y,
      JTMixedGraphOrderedLabel.orderedPoint F =
        pulledLabel W x y (TripleBeadEndpointLabel.code d) u n
          (JTMixedGraphOrderedLabel.orderedPoint E) ∧
      SSet.stdSimplex.map (vertical u n (graphIndex ⦋d⦌ k s 0)) ≫ F.left =
        term (simplex n) ≫ vertexPoint W x ≫ identityFamily W ∧
      SSet.stdSimplex.map (vertical u n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ F.right =
        term (simplex n) ≫ vertexPoint W y ≫ identityFamily W := by
  let j := toFinal u n
  let a := s ≫ J.map (slice u n 0)
  let g := SSet.stdSimplex.map (JTHigherInterleavedParameter.ret b n) ≫ f
  let t := (s ≫ J.map u) ≫ J.map (JTHigherInterleavedParameter.slice b n 0)
  have hj : SSet.stdSimplex.map j ≫ g = f₀ := (toFinal_row u n f).trans hf
  have hs : a ≫ J.map j = t := toFinal_graph u n s
  have H {b₀ : simplex ⦋d⦌ ⟶ J.obj (common b n)} (hs : a ≫ J.map j = b₀)
      (E : EdgeFamilies W ⦋d⦌ (common b n) g b₀ x y)
      {g₀ : simplex (common k n) ⟶ row W ⦋d⦌} (hf₀ : SSet.stdSimplex.map j ≫ g = g₀) :
      ∃ F : EdgeFamilies W ⦋d⦌ (common k n) g₀ a x y,
        JTMixedGraphOrderedLabel.orderedPoint F =
          pulledLabel W x y (TripleBeadEndpointLabel.code d) u n
            (JTMixedGraphOrderedLabel.orderedPoint E) ∧
        F.left = SSet.stdSimplex.map j ≫ E.left ∧
        F.right = SSet.stdSimplex.map j ≫ E.right := by
    subst b₀
    subst g₀
    exact ⟨restrictEdgeFamilies j g a E, orderedPoint_reindex j g a E, rfl, rfl⟩
  obtain ⟨F, hF, hL, hR⟩ := H hs E hj
  refine ⟨F, hF, ?_, ?_⟩
  · rw [hL, ← Category.assoc, ← SSet.stdSimplex.map_comp, vertical_toFinal,
      ← graphIndex_reindex u s]
    exact hleft
  · rw [hR, ← Category.assoc, ← SSet.stdSimplex.map_comp, vertical_toFinal,
      ← graphIndex_reindex u s]
    exact hright

end

end DaggerModels.PartII.JTCommonCoefficientFinalFamilies
