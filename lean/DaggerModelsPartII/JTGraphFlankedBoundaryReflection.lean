import DaggerModelsPartII.JTGraphBeadBoundaryReflection
import DaggerModelsPartII.JTGraphNondegenerateBead
import DaggerModelsPartII.JTNativeFlankedBeadImage
import DaggerModelsPartII.JTNativeJointBoundaryReflection

/-!
# Reflection through a flanked quotient with nonconstant endpoint beads
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace NecklaceCode
open DaggerOriginalFlagFlankification

namespace DaggerModels.PartII.JTGraphFlankedBoundaryReflection

open JTGraphNondegenerateBead (boundary_iff_constant)
open JTGraphBeadBoundaryReflection (ReflectsBeadBoundary)
open JTNativeFlankedBeadImage (flanked_bead_image)
open JTNativeJointBoundaryReflection

noncomputable section

private abbrev term (n : ℕ) := SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{0})

private theorem precompose_term {m n : ℕ} (p : (Δ[m] : SSet.{0}) ⟶ Δ[n]) :
    p ≫ term n = term m := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem term_epi (n : ℕ) : Epi (term n) := by
  haveI : IsSplitEpi (term n) := IsSplitEpi.mk' {
    section_ := SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)
    id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }
  infer_instance

variable {S T L : NecklaceCode} {n : ℕ}
variable (F : Flag.{0} S n) (G : Flag.{0} T n)
variable (g : S ⟶ T) (f : T ⟶ L)
variable (hFG : NecklaceCode.Flag.map g F = G) (hF : Flanked F) (hG : Flanked G)

include hFG hF hG

private theorem reflect_constant (b : S.Bead) (v : Fin (T.len + 1)) (w : Fin (L.len + 1))
    (hBead : ∀ d : T.Bead, T.beadSimplex d ≫ f.map ≠ term d.length ≫ pointAt L (ULift.up w))
    (hJoint : ∀ z ∈ T.joints, orderMap f.map z = w → z = v)
    (h : S.beadSimplex b ≫ (g ≫ f).map = term b.length ≫ pointAt L (ULift.up w)) :
    S.beadSimplex b ≫ g.map = term b.length ≫ pointAt T (ULift.up v) := by
  have hcomp : (S.beadSimplex b ≫ g.map) ≫ f.map = term b.length ≫ pointAt L (ULift.up w) :=
    (Category.assoc _ _ _).trans h
  rcases flanked_bead_image F G g hFG hF hG b with ⟨d, e, he, hd⟩ | ⟨z, hz, hconst⟩
  · exfalso
    apply hBead d
    letI : Epi e := he
    letI : IsSplitEpi e := isSplitEpi_of_epi e
    haveI : IsSplitEpi (SSet.stdSimplex.map e) := by infer_instance
    apply (cancel_epi (SSet.stdSimplex.map e)).mp
    calc
      _ = (S.beadSimplex b ≫ g.map) ≫ f.map :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun u ↦ u ≫ f.map) hd.symm)
      _ = term b.length ≫ pointAt L (ULift.up w) := hcomp
      _ = _ := by rw [← Category.assoc, precompose_term]
  · haveI : Epi (term b.length) := term_epi _
    have hp : pointAt T (ULift.up z) ≫ f.map = pointAt L (ULift.up w) := by
      apply (cancel_epi (term b.length)).mp
      calc
        _ = (S.beadSimplex b ≫ g.map) ≫ f.map :=
          (Category.assoc _ _ _).symm.trans (congrArg (fun u ↦ u ≫ f.map) hconst.symm)
        _ = _ := hcomp
    rw [pointAt_comp] at hp
    have horder : orderMap f.map z = w := by
      have h' := congrArg
        (fun p : (Δ[0] : SSet.{0}) ⟶ L.toSSet ↦ (L.verticesEquiv (SSet.yonedaEquiv p)).down) hp
      simpa only [pointAt_vertex, Equiv.apply_symm_apply] using h'
    rw [hJoint z hz horder] at hconst
    exact hconst

/-- An endpoint-preserving map that takes no full target bead to a constant
endpoint reflects the boundary on the source beads of every flanked quotient. -/
theorem reflects_of_flanked
    (hFirst : ∀ b : T.Bead, T.beadSimplex b ≫ f.map ≠ term b.length ≫ pointAt L (ULift.up 0))
    (hLast : ∀ b : T.Bead, T.beadSimplex b ≫ f.map ≠
      term b.length ≫ pointAt L (ULift.up (Fin.last L.len))) :
    ReflectsBeadBoundary g f := by
  intro b hb
  rcases (boundary_iff_constant L b.length (S.beadSimplex b ≫ (g ≫ f).map)).mp hb with
    h | h
  · apply (boundary_iff_constant T b.length (S.beadSimplex b ≫ g.map)).mpr
    exact Or.inl (reflect_constant F G g f hFG hF hG b 0 0 hFirst
      (fun z hz he ↦ joint_eq_first_of_map_first f hFirst z hz he) h)
  · apply (boundary_iff_constant T b.length (S.beadSimplex b ≫ g.map)).mpr
    exact Or.inr (reflect_constant F G g f hFG hF hG b (Fin.last T.len) (Fin.last L.len)
      hLast (fun z hz he ↦ joint_eq_last_of_map_last f hLast z hz he) h)

end

end DaggerModels.PartII.JTGraphFlankedBoundaryReflection
