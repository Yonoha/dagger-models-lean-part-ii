import DaggerModelsPartII.JTRowGraphDegeneracyNormalization
import DaggerModelsPartII.JTRawVertexRecovery

/-!
# Coefficients of point-supported row graphs
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTRowGraphPointCoefficient

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphCategory
open JTRowGraphNormalForm JTRowGraphResolution JTRowGraphParameterSupport
open JTRowGraphDegeneracyNormalization

noncomputable section

private abbrev row (W : BiPresheaf) (d : SimplexCategory) :=
  (JTRealizationDiagonal.ordinaryCurry.obj W).obj (op d)

/-- The original degree-zero coefficient as a graph over the unique zero parameter. -/
def pointGraph {W : BiPresheaf} (w : W.obj (op (⦋0⦌, ⦋0⦌))) : Graph W ⦋0⦌ :=
  ⟨⦋0⦌, w, JTParameterZero.parameterZeroIsTerminal.from (Δ[0] : SSet.{0})⟩

/-- The graph selects the literal raw vertex of the original coefficient. -/
theorem pointGraph_vertex {W : BiPresheaf} (w : W.obj (op (⦋0⦌, ⦋0⦌))) :
    SSet.yonedaEquiv (pointGraph w).value = JTRawVertexRecovery.zeroVertex W w := by
  have hp : JTParameterZero.parameterZeroIsTerminal.from (Δ[0] : SSet.{0}) =
      JTParameterZero.parameterZeroIso.inv :=
    JTParameterZero.parameterZeroIsTerminal.hom_ext _ _
  unfold pointGraph Graph.value JTRawVertexRecovery.zeroVertex
  rw [hp]
  have hl : lift (𝟙 (Δ[0] : SSet.{0})) JTParameterZero.parameterZeroIso.inv =
      JTGtildeOrderedFiberAction.zeroTensorVertex := rfl
  rw [hl]

private theorem pointGraph_normal {W : BiPresheaf}
    (w : W.obj (op (⦋0⦌, ⦋0⦌))) :
    canonical (pointGraph w).value = pointGraph w := by
  have hc : (pointGraph w).coefficient ∈
      (row W ⦋0⦌).nonDegenerate (pointGraph w).degree.len := by
    simpa only [pointGraph, SimplexCategory.len_mk] using
      (show w ∈ (row W ⦋0⦌).nonDegenerate 0 by
        rw [SSet.nondegenerate_zero]
        trivial)
  have hs : Function.Surjective (label (pointGraph w).parameter) := by
    have : Subsingleton (Fin ((pointGraph w).degree.len + 1)) := by
      change Subsingleton (Fin 1)
      infer_instance
    intro v
    exact ⟨0, Subsingleton.elim _ _⟩
  exact (normal_eq_canonical (pointGraph w)).symm.trans
    (normal_eq_of_reduced (pointGraph w) hc hs)

/-- A graph supported on the original raw point has the exact original coefficient. -/
theorem coefficient_of_point_value {W : BiPresheaf} {d : SimplexCategory}
    (G : Graph W d) (w : W.obj (op (⦋0⦌, ⦋0⦌)))
    (hs : Function.Surjective (label G.parameter))
    (h : G.value = SSet.stdSimplex.map (SimplexCategory.isTerminalZero.from d) ≫
      (pointGraph w).value) :
    G.coefficient = W.map
      (show (d, G.degree) ⟶ (⦋0⦌, ⦋0⦌) from
        (SimplexCategory.isTerminalZero.from d,
          SimplexCategory.isTerminalZero.from G.degree)).op w := by
  let a := SimplexCategory.isTerminalZero.from d
  let b := SimplexCategory.const ⦋0⦌ d 0
  have hab : b ≫ a = 𝟙 ⦋0⦌ := SimplexCategory.isTerminalZero.hom_ext _ _
  have hcanonical : canonical G.value = restrictGraph a (pointGraph w) := by
    rw [h, canonical_restrictGraph_of_splitEpi a b hab, pointGraph_normal]
  let u : G ⟶ restrictGraph a (pointGraph w) :=
    toCanonicalOfSurjective G hs ≫ eqToHom hcanonical
  have hu : u.operator = SimplexCategory.isTerminalZero.from G.degree :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  have hc := u.coefficient
  change W.map (show (d, G.degree) ⟶ (d, ⦋0⦌) from (𝟙 d, u.operator)).op
      (W.map (show (d, ⦋0⦌) ⟶ (⦋0⦌, ⦋0⦌) from (a, 𝟙 ⦋0⦌)).op w) =
    G.coefficient at hc
  have hcomp :
      (show (d, G.degree) ⟶ (d, ⦋0⦌) from (𝟙 d, u.operator)) ≫
          (show (d, ⦋0⦌) ⟶ (⦋0⦌, ⦋0⦌) from (a, 𝟙 ⦋0⦌)) =
        (show (d, G.degree) ⟶ (⦋0⦌, ⦋0⦌) from
          (SimplexCategory.isTerminalZero.from d,
            SimplexCategory.isTerminalZero.from G.degree)) := by
    ext <;> simp [a, hu]
  have hc' : W.map
      ((show (d, G.degree) ⟶ (d, ⦋0⦌) from (𝟙 d, u.operator)) ≫
        (show (d, ⦋0⦌) ⟶ (⦋0⦌, ⦋0⦌) from (a, 𝟙 ⦋0⦌))).op w =
      G.coefficient := by
    simpa only [op_comp, W.map_comp, types_comp_apply] using hc
  rw [hcomp] at hc'
  exact hc'.symm

end

end DaggerModels.PartII.JTRowGraphPointCoefficient
