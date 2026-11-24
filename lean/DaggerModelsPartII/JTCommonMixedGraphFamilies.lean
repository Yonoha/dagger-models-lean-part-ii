import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex
import DaggerModelsPartII.JTInjectiveOrderedEndpointFibration
import DaggerModelsPartII.JTInterleavedParameter
import DaggerModelsPartII.JTEndpointPrismExtension

/-!
# Common mixed graph edge families

Both prescribed edge families live over the same `f`
and `s`.  Two relative endpoint prisms make their left and right maps into
whole maps over the interleaved common simplex.  The common parameter for the
`EdgeFamilies` structure is the zero slice; ordered-label restriction along
both slices is proved from the three full component maps.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
  DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTCommonMixedGraphFamilies

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTInterleavedParameter JTMixedGraphEdgeFamilyReindex
open TripleBeadEndpointLabel JTEndpointNormalizationLifts
open DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev term (K : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from K

private def constant (W : Source) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory) : Δ k ⟶ row W ⦋0⦌ :=
  term (Δ k) ≫ vertexPoint W z

private theorem constant_precomp (W : Source)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    {k l : SimplexCategory} (j : k ⟶ l) :
    SSet.stdSimplex.map j ≫ constant W z l = constant W z k := by
  unfold constant
  rw [← Category.assoc]
  exact congrArg (fun h ↦ h ≫ vertexPoint W z)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private theorem vertex_reindex {k l : SimplexCategory} (j : k ⟶ l)
    (a : Fin (k.len + 1)) :
    vertex k a ≫ SSet.stdSimplex.map j =
      vertex l (j.toOrderHom a) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]

private theorem slice_ret_map (k : SimplexCategory) (v : Fin 2) :
    SSet.stdSimplex.map (slice k v) ≫
      SSet.stdSimplex.map (ret k) = 𝟙 (Δ k) := by
  rw [← SSet.stdSimplex.map_comp, slice_ret, SSet.stdSimplex.{0}.map_id]

/-- Ordered-point naturality uses the full three component maps, independently
of the parameter used to certify the degenerate edges. -/
private theorem orderedPoint_of_components
    {W : Source} {d : ℕ} {k l : SimplexCategory}
    (j : k ⟶ l)
    {fL : Δ l ⟶ row W ⦋d⦌} {sL : Δ ⦋d⦌ ⟶ J l}
    {fK : Δ k ⟶ row W ⦋d⦌} {sK : Δ ⦋d⦌ ⟶ J k}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (E : EdgeFamilies W ⦋d⦌ l fL sL x y)
    (e : EdgeFamilies W ⦋d⦌ k fK sK x y)
    (hleft : SSet.stdSimplex.map j ≫ E.left = e.left)
    (hmiddle : SSet.stdSimplex.map j ≫ fL = fK)
    (hright : SSet.stdSimplex.map j ≫ E.right = e.right) :
    ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (code d))).map j.op (JTMixedGraphOrderedLabel.orderedPoint E) =
      JTMixedGraphOrderedLabel.orderedPoint e := by
  let a := JTMixedGraphOrderedLabel.families E
  let b := JTMixedGraphOrderedLabel.families e
  have hleft' : b.left = SSet.stdSimplex.map j ≫ a.left := by
    dsimp only [a, b, JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc (SSet.stdSimplex.map j), hleft]
  have hmiddle' : b.middle = SSet.stdSimplex.map j ≫ a.middle := by
    dsimp only [a, b, JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc (SSet.stdSimplex.map j), hmiddle]
  have hright' : b.right = SSet.stdSimplex.map j ≫ a.right := by
    dsimp only [a, b, JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc (SSet.stdSimplex.map j), hright]
  have hinner : innerLabel b = SSet.stdSimplex.map j ≫ innerLabel a := by
    apply (wedgeMappingPullback W (single d) (single 1)).hom_ext
    · rw [innerLabel, glue_left, Category.assoc, innerLabel, glue_left]
      exact hmiddle'
    · rw [innerLabel, glue_right, Category.assoc, innerLabel, glue_right]
      exact hright'
  have hcoeff : tripleLabel b = SSet.stdSimplex.map j ≫ tripleLabel a := by
    apply (wedgeMappingPullback W (single 1)
      (wedge (single d) (single 1))).hom_ext
    · rw [tripleLabel, glue_left, Category.assoc, tripleLabel, glue_left]
      exact hleft'
    · rw [tripleLabel, glue_right, Category.assoc, tripleLabel, glue_right]
      exact hinner
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.stdSimplex.map_comp_yonedaEquiv_symm]
  dsimp only [JTMixedGraphOrderedLabel.orderedPoint,
    TripleBeadEndpointLabel.orderedPoint]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  symm
  change pullback.lift (tripleLabel b)
      (term (Δ k)) (tripleLabel_boundary b) =
    SSet.stdSimplex.map j ≫
      pullback.lift (tripleLabel a)
        (term (Δ l)) (tripleLabel_boundary a)
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    exact hcoeff
  · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

set_option maxHeartbeats 800000 in
/-- Simultaneous common coefficient for two original edge families.  The
two ordered points are exactly the restrictions along the two actual slices.
The duplicate edges are constant as whole interval maps, not merely at their
vertices. -/
theorem exists_commonFamilies
    {W : Source} (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W)
    (d : ℕ) (k : SimplexCategory)
    (f : Δ k ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J k)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (e₀ e₁ : EdgeFamilies W ⦋d⦌ k f s x y) :
    ∃ E : EdgeFamilies W ⦋d⦌ (common k)
        (SSet.stdSimplex.map (ret k) ≫ f)
        (s ≫ GroupoidSimplex.parameter.map (slice k 0)) x y,
      SSet.stdSimplex.map (slice k 0) ≫ E.left = e₀.left ∧
      SSet.stdSimplex.map (slice k 1) ≫ E.left = e₁.left ∧
      SSet.stdSimplex.map (slice k 0) ≫ E.right = e₀.right ∧
      SSet.stdSimplex.map (slice k 1) ≫ E.right = e₁.right ∧
      SSet.stdSimplex.map (edge k (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
        term (Δ ⦋1⦌) ≫ (vertexPoint W x ≫ identityFamily W) ∧
      SSet.stdSimplex.map
          (edge k (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
        term (Δ ⦋1⦌) ≫ (vertexPoint W y ≫ identityFamily W) ∧
      ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
          (op (code d))).map (slice k 0).op
            (JTMixedGraphOrderedLabel.orderedPoint E) =
        JTMixedGraphOrderedLabel.orderedPoint e₀ ∧
      ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
          (op (code d))).map (slice k 1).op
            (JTMixedGraphOrderedLabel.orderedPoint E) =
        JTMixedGraphOrderedLabel.orderedPoint e₁ := by
  let K := common k
  let a := graphIndex ⦋d⦌ k s 0
  let b := graphIndex ⦋d⦌ k s (Fin.last d)
  let fK : Δ K ⟶ row W ⦋d⦌ := SSet.stdSimplex.map (ret k) ≫ f
  let sK : Δ ⦋d⦌ ⟶ J K := s ≫ GroupoidSimplex.parameter.map (slice k 0)
  let baseL : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
    prod.lift (constant W x k) (f ≫ rowVertex W ⦋d⦌ 0)
  let baseR : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
    prod.lift (f ≫ rowVertex W ⦋d⦌ (Fin.last d)) (constant W y k)
  let tL : Δ ⦋0⦌ ⟶ row W ⦋1⦌ :=
    vertexPoint W x ≫ identityFamily W
  let tR : Δ ⦋0⦌ ⟶ row W ⦋1⦌ :=
    vertexPoint W y ≫ identityFamily W
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  obtain ⟨L, hL₀, hL₁, hLa, hLp⟩ :=
    JTEndpointPrismExtension.exists_extension k a (endpointArrow W)
      baseL tL e₀.left e₁.left e₀.left_boundary e₁.left_boundary
      e₀.left_degenerate e₁.left_degenerate
  obtain ⟨R, hR₀, hR₁, hRb, hRp⟩ :=
    JTEndpointPrismExtension.exists_extension k b (endpointArrow W)
      baseR tR e₀.right e₁.right e₀.right_boundary e₁.right_boundary
      e₀.right_degenerate e₁.right_degenerate
  have hLK : L ≫ endpointArrow W =
      prod.lift (constant W x K) (fK ≫ rowVertex W ⦋d⦌ 0) := by
    rw [hLp]
    dsimp only [baseL, fK]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.comp_lift, prod.lift_fst]
      exact constant_precomp W x (ret k)
    · simp only [Category.assoc, prod.comp_lift, prod.lift_snd]
  have hRK : R ≫ endpointArrow W =
      prod.lift (fK ≫ rowVertex W ⦋d⦌ (Fin.last d))
        (constant W y K) := by
    rw [hRp]
    dsimp only [baseR, fK]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.comp_lift, prod.lift_fst]
    · simp only [Category.assoc, prod.comp_lift, prod.lift_snd]
      exact constant_precomp W y (ret k)
  have haK : graphIndex ⦋d⦌ K sK 0 =
      (slice k 0).toOrderHom a := by
    exact graphIndex_reindex (slice k 0) s 0
  have hbK : graphIndex ⦋d⦌ K sK (Fin.last d) =
      (slice k 0).toOrderHom b := by
    exact graphIndex_reindex (slice k 0) s (Fin.last d)
  let E : EdgeFamilies W ⦋d⦌ K fK sK x y :=
    { left := L
      right := R
      left_boundary := hLK
      right_boundary := hRK
      left_degenerate := by
        change vertex K (graphIndex ⦋d⦌ K sK 0) ≫ L = tL
        rw [haK, ← vertex_reindex (slice k 0) a, Category.assoc, hL₀]
        exact e₀.left_degenerate
      right_degenerate := by
        change vertex K (graphIndex ⦋d⦌ K sK (Fin.last d)) ≫ R = tR
        rw [hbK, ← vertex_reindex (slice k 0) b, Category.assoc, hR₀]
        exact e₀.right_degenerate }
  have hf₀ : SSet.stdSimplex.map (slice k 0) ≫ fK = f := by
    dsimp [fK]
    rw [← Category.assoc, slice_ret_map, Category.id_comp]
  have hf₁ : SSet.stdSimplex.map (slice k 1) ≫ fK = f := by
    dsimp [fK]
    rw [← Category.assoc, slice_ret_map, Category.id_comp]
  refine ⟨E, hL₀, hL₁, hR₀, hR₁, hLa, hRb, ?_, ?_⟩
  · exact orderedPoint_of_components (slice k 0) E e₀ hL₀ hf₀ hR₀
  · exact orderedPoint_of_components (slice k 1) E e₁ hL₁ hf₁ hR₁

end

end DaggerModels.PartII.JTCommonMixedGraphFamilies
