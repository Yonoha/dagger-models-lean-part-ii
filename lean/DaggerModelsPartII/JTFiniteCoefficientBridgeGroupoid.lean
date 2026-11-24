import DaggerModelsPartII.JTFiniteCoefficientBridgePrism
import DaggerModelsPartII.JTCommonCoefficientGroupoidPrism
import DaggerModelsPartII.JTCodiscreteParameterPairing

/-!
# The full groupoid prism for a finite family of coefficient orders
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeGroupoid

open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgePrism
open JTHigherInterleavedParameter (common)
open JTParameterContraction
open JTCodiscreteParameterPairing (coord coord_map coord_vertex pairBy coord_pairBy)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev unit := JTCylinderCEComparison.simplexUnit

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)

/-- Use the same joining vertices in the literal codiscrete parameters. -/
def paired : J.obj k ⊗ J.obj (time m n) ⟶ J.obj (bridge k n m) :=
  pairBy (rankVertex c u n)

theorem paired_base :
    paired c u n ≫ J.map (base c u n) =
      fst (J.obj k) (J.obj (time m n)) ≫ J.map u := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((J.map (base c u n)).app q ((pairBy (rankVertex c u n)).app q z)) v =
    coord _ q ((J.map u).app q z.1) v
  rw [coord_map, coord_map, coord_pairBy]
  obtain ⟨⟨e, t⟩, ht⟩ := (timeVertexEquiv m n).surjective (coord (time m n) q z.2 v)
  rw [← ht, rankVertex_apply, base_vertexEquiv]

theorem paired_vertex (a : Fin (k.len + 1)) :
    (parameterVertex k a ⊗ₘ 𝟙 (J.obj (time m n))) ≫ paired c u n =
      snd (Δ[0] : SSet.{0}) (J.obj (time m n)) ≫ J.map (vertical c u n a) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c u n)).app q ((parameterVertex k a).app q z.1, z.2)) v =
    coord _ q ((J.map (vertical c u n a)).app q z.2) v
  rw [coord_pairBy, coord_vertex, coord_map]
  rfl

theorem paired_slice (t : Fin ((time m n).len + 1)) :
    JTHigherGroupoidParameterPrism.timeSlice (J.obj k) (time m n) t ≫ paired c u n =
      J.map (slice c u n t) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c u n)).app q (z,
      (parameterVertex (time m n) t).app q ((SSet.stdSimplex.isTerminalObj₀.from _).app q z))) v =
    coord _ q ((J.map (slice c u n t)).app q z) v
  rw [coord_pairBy, coord_vertex, coord_map]
  rfl

variable (h : ∀ e, b e ⟶ b') (hu : ∀ e, c e ≫ h e = u)

/-- The original common-coefficient pairing on every side. -/
theorem paired_side (e : Fin (m + 1)) :
    (J.obj k ◁ J.map (timeSide n e)) ≫ paired c u n =
      JTCommonCoefficientParameter.paired (c e) n ≫ J.map (side c u h hu n e) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c u n)).app q
    (z.1, (J.map (timeSide n e)).app q z.2)) v =
    coord _ q ((J.map (side c u h hu n e)).app q
      ((pairBy (JTCommonCoefficientParameter.vertexEquiv (c e) n)).app q z)) v
  rw [coord_pairBy, coord_map, coord_map, coord_pairBy]
  change rankVertex c u n (coord k q z.1 v, timeVertexEquiv m n (e, coord n q z.2 v)) = _
  rw [rankVertex_apply, side_vertexEquiv]

/-- The full groupoid pairing restricts to the actual ordinary joining prism. -/
theorem paired_simplexUnit :
    (unit.app k ⊗ₘ unit.app (time m n)) ≫ paired c u n =
      prism c u n ≫ unit.app (bridge k n m) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c u n)).app q
      ((unit.app k).app q z.1, (unit.app (time m n)).app q z.2)) v =
    (SSet.stdSimplex.objEquiv ((prism c u n).app q z)).toOrderHom v
  rw [coord_pairBy, prism_app]
  rfl

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeGroupoid
