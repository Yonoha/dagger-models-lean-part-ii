import DaggerModelsPartII.JTRealizedLabelEndpoints

/-!
# The original strict row coefficient realizes to the entire coend generator
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTRowRealizationGenerator

open ReversalDiscreteFreeColimits JTProjectiveOrderedFiberComparison
open OrderedSimplexEndpointFiber JTNecklaceLabelRealization

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}

private def identitySimplex (k : SimplexCategory) :
    (SSet.stdSimplex.{0}.obj k).obj (op k) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 k)

/-- The original strict free-simplex coefficient corresponding to a row point. -/
def rowCoefficient (W : Source) (m : ℕ) (k : SimplexCategory)
    (w : (row W ⦋m⦌).obj (op k)) :
    (diagramMappingSpace (F.obj (Δ[m] : SSet.{0})) W).obj (op k) :=
  (freeSimplexRowIso W m).inv.app (op k) w

theorem rowCoefficient_on_freeUnit (W : Source) (m : ℕ) (k : SimplexCategory)
    (w : (row W ⦋m⦌).obj (op k)) :
    ((rowCoefficient W m k w).app (op (ReverseSimplex.inclusion.obj ⦋m⦌))).app
        (op k)
        (((freeDaggerAdjunction.unit.app (Δ[m] : SSet.{0})).app (op ⦋m⦌)
          (identitySimplex ⦋m⦌)), identitySimplex k) = w := by
  let c := ReverseSimplex.inclusion.obj ⦋m⦌
  let η := rowCoefficient W m k w
  have hh := congrFun (NatTrans.congr_app (freeSimplexRowIso W m).inv_hom_id (op k)) w
  change (freeSimplexRowIso W m).hom.app (op k) η = w at hh
  change (η.app (op c)).app (op k)
    (((freeDaggerAdjunction.unit.app (Δ[m] : SSet.{0})).app (op ⦋m⦌)
      (identitySimplex ⦋m⦌)), identitySimplex k) = w
  let e := SegalRepresentables.freeSimplexRepresentable.{0} m
  let η' := (diagramMappingPrecomp e.inv W).app (op k) η
  change (tensorYonedaMappingIso W c).hom.app (op k) η' = w at hh
  rw [tensorYonedaMappingIso_apply] at hh
  change (η.app (op c)).app (op k)
    ((e.inv.app (op c)).app (op k) (ULift.up (𝟙 c)), identitySimplex k) = w at hh
  -- Normalize the free representable's identity before evaluating the coefficient.
  have he := ActualUnitNativeComparison.freeSimplexRepresentable_unit_id m (op k)
  change (e.hom.app (op c)).app (op k)
      ((freeDaggerAdjunction.unit.app (Δ[m] : SSet.{0})).app (op ⦋m⦌)
        (identitySimplex ⦋m⦌)) = ULift.up (𝟙 c) at he
  have hi := congrFun (NatTrans.congr_app (NatTrans.congr_app e.hom_inv_id (op c)) (op k))
    ((freeDaggerAdjunction.unit.app (Δ[m] : SSet.{0})).app (op ⦋m⦌)
      (identitySimplex ⦋m⦌))
  change (e.inv.app (op c)).app (op k)
    ((e.hom.app (op c)).app (op k)
      ((freeDaggerAdjunction.unit.app (Δ[m] : SSet.{0})).app (op ⦋m⦌)
        (identitySimplex ⦋m⦌))) = _ at hi
  rw [he] at hi
  simpa only [hi] using hh

/-- The whole `Δ[m] ⊗ J[k]` map agrees with the literal generator. -/
theorem realizedRowCoefficient_eq_generator (W : Source) (m : ℕ) (k : SimplexCategory)
    (w : (row W ⦋m⦌).obj (op k)) :
    realizedLabel (Δ[m] : SSet.{0}) W k (rowCoefficient W m k w) =
      JTRealizationGenerators.generator (JTReversalInput.ordinaryInput.obj W)
        (⦋m⦌, k) w := by
  have hf := realizedLabel_generator_formula (Δ[m] : SSet.{0}) W k ⦋m⦌ k
    (rowCoefficient W m k w) (identitySimplex ⦋m⦌) (identitySimplex k)
  have hi : SSet.yonedaEquiv.symm (identitySimplex ⦋m⦌) =
      𝟙 (Δ[m] : SSet.{0}) := by
    apply SSet.yonedaEquiv.injective
    rfl
  have hk : SSet.stdSimplex.objEquiv (identitySimplex k) = 𝟙 k :=
    Equiv.apply_symm_apply _ _
  rw [hi, hk, GroupoidSimplex.parameter.map_id, id_tensorHom_id, Category.id_comp,
    rowCoefficient_on_freeUnit] at hf
  exact hf

end

end DaggerModels.PartII.JTRowRealizationGenerator
