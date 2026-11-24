import DaggerModelsPartII.JTFiniteCoefficientBridgeMixedOrder
import DaggerModelsPartII.JTFiniteCoefficientBridgeTimeReindex
import DaggerModelsPartII.JTFiniteCoefficientBridgeGroupoid

/-! Ordinary and groupoid bridge prisms in all three varying indices. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeMixedPrism

open JTFiniteCoefficientBridgeOrder (bridge vertexEquiv)
open JTFiniteCoefficientBridgeTime (time timeVertexEquiv)
open JTFiniteCoefficientBridgePrism
open JTFiniteCoefficientBridgeGroupoid (paired)
open JTCodiscreteParameterPairing (coord coord_map pairBy coord_pairBy)

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{v}.obj a
private abbrev J := GroupoidSimplex.parameter

variable {m m' : ℕ} {k l n n' b : SimplexCategory}
variable {B : Fin (m + 1) → SimplexCategory} {C : Fin (m' + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ B e) (d : ∀ e, l ⟶ C e)
variable (f : k ⟶ l) (j : n ⟶ n') (a : ⦋m⦌ ⟶ ⦋m'⦌)
variable {u : k ⟶ b} {u' : l ⟶ b}
variable (hu : f ≫ u' = u) (ha : Function.Injective a.toOrderHom)
variable (hr : JTFiniteCoefficientBridgeMixedOrder.RespectsRanks c d f j a)

private abbrev coefficientMap := JTFiniteCoefficientBridgeMixedOrder.map c d f j a hu ha hr
private abbrev timeMap := JTFiniteCoefficientBridgeTimeReindex.map a ha j

theorem rankVertex_map (x : Fin (k.len + 1) × Fin ((time m n).len + 1)) :
    (coefficientMap c d f j a hu ha hr).toOrderHom (rankVertex c u n x) =
      rankVertex d u' n' (f.toOrderHom x.1, (timeMap j a ha).toOrderHom x.2) := by
  obtain ⟨y, t⟩ := x
  obtain ⟨⟨e, s⟩, rfl⟩ := (timeVertexEquiv m n).surjective t
  change (coefficientMap c d f j a hu ha hr).toOrderHom
      (rankVertex c u n (y, timeVertexEquiv m n (e, s))) =
    rankVertex d u' n' (f.toOrderHom y, (timeMap j a ha).toOrderHom (timeVertexEquiv m n (e, s)))
  rw [rankVertex_apply, JTFiniteCoefficientBridgeMixedOrder.map_vertex,
    JTFiniteCoefficientBridgeTimeReindex.map_vertex, rankVertex_apply]

/-- The entire bridge prism reindexes, including simplices crossing copies. -/
theorem prism_map :
    prism.{v} c u n ≫ SSet.stdSimplex.map (coefficientMap c d f j a hu ha hr) =
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map (timeMap j a ha)) ≫ prism d u' n' := by
  apply NatTrans.ext
  funext q z
  apply SSet.stdSimplex.objEquiv.injective
  ext x : 3
  change (coefficientMap c d f j a hu ha hr).toOrderHom
      ((SSet.stdSimplex.objEquiv ((prism c u n).app q z)).toOrderHom x) =
    (SSet.stdSimplex.objEquiv ((prism d u' n').app q
      ((SSet.stdSimplex.map f).app q z.1, (SSet.stdSimplex.map (timeMap j a ha)).app q z.2))).toOrderHom x
  rw [prism_app, prism_app]
  exact rankVertex_map c d f j a hu ha hr _

/-- The codiscrete parameters have the identical coordinate formula in every degree. -/
theorem paired_map :
    paired c u n ≫ J.map (coefficientMap c d f j a hu ha hr) =
      (J.map f ⊗ₘ J.map (timeMap j a ha)) ≫ paired d u' n' := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z x
  change coord _ q ((J.map (coefficientMap c d f j a hu ha hr)).app q
      ((pairBy (rankVertex c u n)).app q z)) x =
    coord _ q ((pairBy (rankVertex d u' n')).app q
      ((J.map f).app q z.1, (J.map (timeMap j a ha)).app q z.2)) x
  rw [coord_map, coord_pairBy, coord_pairBy, coord_map, coord_map]
  exact rankVertex_map c d f j a hu ha hr _

/-- The stationary coefficient line is preserved with the full joining time. -/
theorem vertical_map (x : Fin (k.len + 1)) :
    vertical c u n x ≫ coefficientMap c d f j a hu ha hr =
      timeMap j a ha ≫ vertical d u' n' (f.toOrderHom x) := by
  ext t : 3
  exact rankVertex_map c d f j a hu ha hr (x, t)

/-- Each coefficient slice is also preserved with its actual image time vertex. -/
theorem slice_map (t : Fin ((time m n).len + 1)) :
    slice c u n t ≫ coefficientMap c d f j a hu ha hr =
      f ≫ slice d u' n' ((timeMap j a ha).toOrderHom t) := by
  ext x : 3
  exact rankVertex_map c d f j a hu ha hr (x, t)

end
end DaggerModels.PartII.JTFiniteCoefficientBridgeMixedPrism
