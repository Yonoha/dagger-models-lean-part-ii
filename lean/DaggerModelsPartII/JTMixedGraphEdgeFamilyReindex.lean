import DaggerModelsPartII.JTMixedGraphOrderedLabel
import DaggerModelsPartII.JTParameterBlocks

/-!
# Parameter reindexing for the original mixed graph edge families

The full ordered-label equation is retained after any parameter operator.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphEdgeFamilyReindex

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open TripleBeadEndpointLabel JTEndpointNormalizationLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k

private theorem parameterIndex_parameterVertex (k : SimplexCategory)
    (i : Fin (k.len + 1)) :
    JTRawVertexRecovery.parameterIndex k
        (JTParameterContraction.parameterVertex k i) = i := by
  rw [← JTParameterVertexKan.simplexUnit_vertex]
  rfl

/-- The graph's selected parameter vertex is natural in its simplex degree. -/
theorem graphIndex_reindex {k l : SimplexCategory} (j : k ⟶ l)
    {d : ℕ} (s : Δ ⦋d⦌ ⟶ J k) (i : Fin (d + 1)) :
    graphIndex ⦋d⦌ l (s ≫ GroupoidSimplex.parameter.map j) i =
      j.toOrderHom (graphIndex ⦋d⦌ k s i) := by
  have h : vertex ⦋d⦌ i ≫ (s ≫ GroupoidSimplex.parameter.map j) =
      JTParameterContraction.parameterVertex l
        (j.toOrderHom (graphIndex ⦋d⦌ k s i)) := by
    calc
      vertex ⦋d⦌ i ≫ (s ≫ GroupoidSimplex.parameter.map j) =
          (vertex ⦋d⦌ i ≫ s) ≫ GroupoidSimplex.parameter.map j := by
            rw [Category.assoc]
      _ = JTParameterContraction.parameterVertex k
            (graphIndex ⦋d⦌ k s i) ≫ GroupoidSimplex.parameter.map j := by
            rw [graphIndex_vertex]
      _ = _ := JTParameterBlocks.parameterVertex_map j _
  have hindex := congrArg (JTRawVertexRecovery.parameterIndex l) h
  simpa only [graphIndex, parameterIndex_parameterVertex] using hindex

private theorem vertex_reindex {k l : SimplexCategory} (j : k ⟶ l)
    (i : Fin (k.len + 1)) :
    vertex k i ≫ SSet.stdSimplex.map j = vertex l (j.toOrderHom i) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp]
  rw [SimplexCategory.const_comp]

set_option maxHeartbeats 800000 in
/-- Precomposition keeps both complete endpoint squares and both original
selected degenerate faces. -/
def restrictEdgeFamilies {W : Source} {d : ℕ} {k l : SimplexCategory}
    (j : k ⟶ l) (f : Δ l ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J k)
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (e : EdgeFamilies W ⦋d⦌ l f
      (s ≫ GroupoidSimplex.parameter.map j) x y) :
    EdgeFamilies W ⦋d⦌ k (SSet.stdSimplex.map j ≫ f) s x y where
  left := SSet.stdSimplex.map j ≫ e.left
  right := SSet.stdSimplex.map j ≫ e.right
  left_boundary := by
    apply prod.hom_ext
    · simp only [Category.assoc, e.left_boundary, prod.lift_fst]
      have ht : SSet.stdSimplex.map j ≫ SSet.stdSimplex.isTerminalObj₀.from (Δ l) =
          SSet.stdSimplex.isTerminalObj₀.from (Δ k) :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ vertexPoint W x) ht
    · simp only [Category.assoc, e.left_boundary, prod.lift_snd]
  right_boundary := by
    apply prod.hom_ext
    · simp only [Category.assoc, e.right_boundary, prod.lift_fst]
    · simp only [Category.assoc, e.right_boundary, prod.lift_snd]
      have ht : SSet.stdSimplex.map j ≫ SSet.stdSimplex.isTerminalObj₀.from (Δ l) =
          SSet.stdSimplex.isTerminalObj₀.from (Δ k) :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ vertexPoint W y) ht
  left_degenerate := by
    calc
      vertex k (graphIndex ⦋d⦌ k s 0) ≫
          (SSet.stdSimplex.map j ≫ e.left) =
          vertex l (graphIndex ⦋d⦌ l
            (s ≫ GroupoidSimplex.parameter.map j) 0) ≫ e.left := by
            rw [← Category.assoc, vertex_reindex, graphIndex_reindex]
      _ = vertexPoint W x ≫ identityFamily W := e.left_degenerate
  right_degenerate := by
    calc
      vertex k (graphIndex ⦋d⦌ k s (Fin.last d)) ≫
          (SSet.stdSimplex.map j ≫ e.right) =
          vertex l (graphIndex ⦋d⦌ l
            (s ≫ GroupoidSimplex.parameter.map j) (Fin.last d)) ≫ e.right := by
            rw [← Category.assoc, vertex_reindex, graphIndex_reindex]
      _ = vertexPoint W y ≫ identityFamily W := e.right_degenerate

private theorem tripleLabel_reindex {W : Source} {d : ℕ}
    {k l : SimplexCategory} (j : k ⟶ l)
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (a : Families W d l x y) (b : Families W d k x y)
    (hleft : b.left = SSet.stdSimplex.map j ≫ a.left)
    (hmiddle : b.middle = SSet.stdSimplex.map j ≫ a.middle)
    (hright : b.right = SSet.stdSimplex.map j ≫ a.right) :
    tripleLabel b = SSet.stdSimplex.map j ≫ tripleLabel a := by
  have hinner : innerLabel b = SSet.stdSimplex.map j ≫ innerLabel a := by
    apply (wedgeMappingPullback W (single d) (single 1)).hom_ext
    · rw [innerLabel, glue_left, Category.assoc, innerLabel, glue_left]
      exact hmiddle
    · rw [innerLabel, glue_right, Category.assoc, innerLabel, glue_right]
      exact hright
  apply (wedgeMappingPullback W (single 1)
    (wedge (single d) (single 1))).hom_ext
  · rw [tripleLabel, glue_left, Category.assoc, tripleLabel, glue_left]
    exact hleft
  · rw [tripleLabel, glue_right, Category.assoc, tripleLabel, glue_right]
    exact hinner

/-- Restriction of a complete ordered three-bead label is determined by
the restrictions of its three row maps. -/
theorem orderedPoint_reindex_of_rows {W : Source} {d : ℕ}
    {k l : SimplexCategory} (j : k ⟶ l)
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (a : Families W d l x y) (b : Families W d k x y)
    (hleft : b.left = SSet.stdSimplex.map j ≫ a.left)
    (hmiddle : b.middle = SSet.stdSimplex.map j ≫ a.middle)
    (hright : b.right = SSet.stdSimplex.map j ≫ a.right) :
    TripleBeadEndpointLabel.orderedPoint b =
      ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (code d))).map j.op (TripleBeadEndpointLabel.orderedPoint a) := by
  have hcoeff := tripleLabel_reindex j a b hleft hmiddle hright
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.stdSimplex.map_comp_yonedaEquiv_symm]
  dsimp only [TripleBeadEndpointLabel.orderedPoint]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change pullback.lift (tripleLabel b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ k)) (tripleLabel_boundary b) =
    SSet.stdSimplex.map j ≫
      pullback.lift (tripleLabel a)
        (SSet.stdSimplex.isTerminalObj₀.from (Δ l)) (tripleLabel_boundary a)
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    exact hcoeff
  · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _


/-- The original ordered point restricts exactly along the simplex operator. -/
theorem orderedPoint_reindex {W : Source} {d : ℕ}
    {k l : SimplexCategory} (j : k ⟶ l)
    (f : Δ l ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J k)
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (e : EdgeFamilies W ⦋d⦌ l f
      (s ≫ GroupoidSimplex.parameter.map j) x y) :
    JTMixedGraphOrderedLabel.orderedPoint
        (restrictEdgeFamilies j f s e) =
      ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (code d))).map j.op
          (JTMixedGraphOrderedLabel.orderedPoint e) := by
  let a := JTMixedGraphOrderedLabel.families e
  let b := JTMixedGraphOrderedLabel.families (restrictEdgeFamilies j f s e)
  apply orderedPoint_reindex_of_rows j a b <;>
    dsimp only [a, b, JTMixedGraphOrderedLabel.families, restrictEdgeFamilies] <;>
    rw [Category.assoc]

end

end DaggerModels.PartII.JTMixedGraphEdgeFamilyReindex
