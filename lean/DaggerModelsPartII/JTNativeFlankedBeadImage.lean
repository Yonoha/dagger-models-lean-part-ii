import OriginalFlagFlankedBeadOperators
import OriginalFlagNormalizationJointImages
import ChosenNecklacePointMaps

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerModels.PartII.JTNativeFlankedBeadImage

noncomputable section

variable {S T : NecklaceCode} {n : ℕ}
variable (F : Flag.{u} S n) (G : Flag.{u} T n)
variable (f : NecklaceCode.Hom.{u} S T)
variable (hfg : NecklaceCode.Flag.map f F = G)
variable (hF : Flanked F) (hG : Flanked G)

include hfg hF hG in
/-- A bead collapsed by a flanked map is the constant simplex at its image joint. -/
theorem collapsed_bead_triangle (b : S.Bead)
    (hb : orderMap f.map b.left = orderMap f.map b.right) :
    orderMap f.map b.left ∈ T.joints ∧
      S.beadSimplex b ≫ f.map =
        SSet.stdSimplex.isTerminalObj₀.from (Δ[b.length] : SSet.{u}) ≫
          pointAt T (ULift.up (orderMap f.map b.left)) := by
  have hc := flanked_arrow_collapsed_bead F G f hfg hF hG b hb
  refine ⟨hc.1, ?_⟩
  have hterminal : SSet.stdSimplex.isTerminalObj₀.from (Δ[b.length] : SSet.{u}) =
      SSet.stdSimplex.map (SimplexCategory.const ⦋b.length⦌ ⦋0⦌ 0) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hterminal]
  apply (cancel_mono T.inclusion).1
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  apply stdSimplex_hom_ext
  intro x
  apply SSet.stdSimplex.ext
  intro i
  change orderMap f.map
      ((S.inclusion.app _ (S.beadSimplex b |>.app _ x)) i) =
    T.inclusion.app _
      ((pointAt T (ULift.up (orderMap f.map b.left))).app _
        ((SSet.stdSimplex.map
          (SimplexCategory.const ⦋b.length⦌ ⦋0⦌ 0)).app _ x)) i
  rw [b.beadSimplex_inclusion_apply, pointAt_inclusion_apply]
  exact hc.2 _ (Finset.orderEmbOfFin_mem b.interval b.card_interval (x i))

include hfg hF hG in
/-- Every source bead maps either onto an actual target bead or to a target joint. -/
theorem flanked_bead_image (b : S.Bead) :
    (∃ d : T.Bead, ∃ e : ⦋b.length⦌ ⟶ ⦋d.length⦌,
      Epi e ∧ S.beadSimplex b ≫ f.map =
        SSet.stdSimplex.map e ≫ T.beadSimplex d) ∨
    (∃ v : Fin (T.len + 1), v ∈ T.joints ∧
      S.beadSimplex b ≫ f.map =
        SSet.stdSimplex.isTerminalObj₀.from (Δ[b.length] : SSet.{u}) ≫
          pointAt T (ULift.up v)) := by
  by_cases hb : orderMap f.map b.left = orderMap f.map b.right
  · right
    exact ⟨orderMap f.map b.left, collapsed_bead_triangle F G f hfg hF hG b hb⟩
  · have hp : orderMap f.map b.left < orderMap f.map b.right :=
      lt_of_le_of_ne ((orderMap f.map).monotone b.lt.le) hb
    left
    exact ⟨flankedImageBead F G f hfg hF hG b hp,
      flankedBeadOperator F G f hfg hF hG b hp,
      flankedBeadOperator_epi F G f hfg hF hG b hp,
      flankedBeadOperator_triangle F G f hfg hF hG b hp⟩

end

end DaggerModels.PartII.JTNativeFlankedBeadImage
