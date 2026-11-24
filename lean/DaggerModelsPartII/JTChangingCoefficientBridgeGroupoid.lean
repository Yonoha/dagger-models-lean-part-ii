import DaggerModelsPartII.JTChangingCoefficientBridgePrism
import DaggerModelsPartII.JTCommonCoefficientGroupoidPrism
import DaggerModelsPartII.JTCodiscreteParameterPairing

/-!
# The full groupoid prism across a change of coefficient
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTChangingCoefficientBridgeGroupoid

open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgePrism
open JTHigherInterleavedParameter (common)
open JTParameterContraction
open JTCodiscreteParameterPairing (coord coord_map coord_vertex pairBy coord_pairBy)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev unit := JTCylinderCEComparison.simplexUnit

variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)

/-- Use the same joining vertices in the literal codiscrete parameters. -/
def paired : J.obj k ⊗ J.obj (time n) ⟶ J.obj (bridge k n) :=
  pairBy (rankVertex c h n)

theorem paired_base :
    paired c h n ≫ J.map (base c h n) =
      fst (J.obj k) (J.obj (time n)) ≫ J.map (c ≫ h) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((J.map (base c h n)).app q ((pairBy (rankVertex c h n)).app q z)) v =
    coord _ q ((J.map (c ≫ h)).app q z.1) v
  rw [coord_map, coord_map, coord_pairBy]
  obtain ⟨⟨e, t⟩, ht⟩ := (timeVertexEquiv n).surjective (coord (time n) q z.2 v)
  rw [← ht, rankVertex_apply, base_vertexEquiv]

theorem paired_vertex (a : Fin (k.len + 1)) :
    (parameterVertex k a ⊗ₘ 𝟙 (J.obj (time n))) ≫ paired c h n =
      snd (Δ[0] : SSet.{0}) (J.obj (time n)) ≫ J.map (vertical c h n a) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c h n)).app q ((parameterVertex k a).app q z.1, z.2)) v =
    coord _ q ((J.map (vertical c h n a)).app q z.2) v
  rw [coord_pairBy, coord_vertex, coord_map]
  rfl

theorem paired_slice (t : Fin ((time n).len + 1)) :
    JTHigherGroupoidParameterPrism.timeSlice (J.obj k) (time n) t ≫ paired c h n =
      J.map (slice c h n t) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c h n)).app q (z,
      (parameterVertex (time n) t).app q ((SSet.stdSimplex.isTerminalObj₀.from _).app q z))) v =
    coord _ q ((J.map (slice c h n t)).app q z) v
  rw [coord_pairBy, coord_vertex, coord_map]
  rfl

abbrev sidePaired (e : Fin 2) : J.obj k ⊗ J.obj n ⟶ J.obj (common k n) :=
  if e = 0 then JTCommonCoefficientParameter.paired c n
  else JTCommonCoefficientParameter.paired (c ≫ h) n

/-- The two exact ordinary overlap squares extend to the full groupoid parameters. -/
theorem paired_side (e : Fin 2) :
    (J.obj k ◁ J.map (timeSide n e)) ≫ paired c h n =
      sidePaired c h n e ≫ J.map (side c h n e) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c h n)).app q
    (z.1, (J.map (timeSide n e)).app q z.2)) v =
    coord _ q ((J.map (side c h n e)).app q ((sidePaired c h n e).app q z)) v
  rw [coord_pairBy, coord_map, coord_map]
  change rankVertex c h n (coord k q z.1 v, timeVertexEquiv n (e, coord n q z.2 v)) = _
  rw [rankVertex_apply]
  fin_cases e
  · change _ = (side c h n 0).toOrderHom
      (coord _ q ((pairBy (JTCommonCoefficientParameter.vertexEquiv c n)).app q z) v)
    rw [coord_pairBy, side_vertexEquiv_zero]
    rfl
  · change _ = (side c h n 1).toOrderHom
      (coord _ q ((pairBy (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n)).app q z) v)
    rw [coord_pairBy, side_vertexEquiv_one]
    rfl

/-- The full groupoid pairing restricts to the actual ordinary joining prism. -/
theorem paired_simplexUnit :
    (unit.app k ⊗ₘ unit.app (time n)) ≫ paired c h n =
      prism c h n ≫ unit.app (bridge k n) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord _ q ((pairBy (rankVertex c h n)).app q
      ((unit.app k).app q z.1, (unit.app (time n)).app q z.2)) v =
    (SSet.stdSimplex.objEquiv ((prism c h n).app q z)).toOrderHom v
  rw [coord_pairBy, prism_app]
  rfl

end

end DaggerModels.PartII.JTChangingCoefficientBridgeGroupoid
