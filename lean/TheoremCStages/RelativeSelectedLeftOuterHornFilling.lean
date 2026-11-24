import RelativeLeftOuterHornFilling
import RelativeRightOuterHornFilling
import OriginalInnerHornFillersReversal
import OriginalHomotopyCategoryOppositeComparison

/-!
# Selected relative left outer horns by exact reversal

Only the original first edge of the supplied left outer horn is required to
be invertible. Reversal carries that same edge to the selected last edge of
the right outer horn in the opposite simplicial set. The relative right-horn
filler is transported back with its entire prescribed base simplex. No full
outer-horn lifting-property hypothesis is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalHomotopyCategoryOppositeComparison
open DaggerOriginalHornFillingReversal
open DaggerModels.PartII.RelativeHornFillingReversal
open DaggerModels.PartII.RelativeHornReversedExtension
open DaggerModels.PartII.RelativeLeftOuterHornGeometry
open DaggerModels.PartII.RelativeLeftOuterHornFilling
open DaggerOriginalRelativeRightOuterHornFilling

universe u

namespace DaggerModels.PartII.RelativeSelectedLeftOuterHornFilling

noncomputable section

/-- At degree one, the opposite of the original edge is exactly evaluation
after the standard-simplex reversal, with its original vertex order. -/
private theorem yoneda_reversed_edge {C : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.yonedaEquiv
        (DaggerOriginalStandardSimplexReversal.standardSimplexReversalInv 1 ≫
          SSet.opFunctor.map e) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv e) := by
  have hid : SSet.yonedaEquiv
      (DaggerOriginalStandardSimplexReversal.standardSimplexReversalInv 1 :
        (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}).op) =
      SSet.opObjEquiv.symm (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by
    apply SSet.opObjEquiv.injective
    apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (𝟙 ⦋1⦌) = 𝟙 ⦋1⦌
    exact SimplexCategory.rev.map_id ⦋1⦌
  rw [SSet.yonedaEquiv_comp, hid, SSet.opFunctor_map]
  rfl

/-- The literal first edge of a left outer horn controls one selected
relative filler, retaining its original horn and prescribed base simplex. -/
theorem selected_left_outer_horn_filler_over {C D : SSet.{u}} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (k : ℕ)
    (φ : (Λ[k + 2, (0 : Fin (k + 3))] : SSet.{u}) ⟶ C)
    (β : (Δ[k + 2] : SSet.{u}) ⟶ D)
    (w : φ ≫ p = Λ[k + 2, (0 : Fin (k + 3))].ι ≫ β)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (firstEdgeInclusion k ≫ φ))) :
    ∃ σ : (Δ[k + 2] : SSet.{u}) ⟶ C,
      φ = Λ[k + 2, (0 : Fin (k + 3))].ι ≫ σ ∧ σ ≫ p = β := by
  have hpOp : DaggerNativeInnerHornFactorization.innerFibrations
      (SSet.opFunctor.map p) := innerFibrations_op p hp
  have hCOp : innerHornFillers C.op :=
    DaggerOriginalInnerHornFillersReversal.innerHornFillers_op hC
  have hDOp : innerHornFillers D.op :=
    DaggerOriginalInnerHornFillersReversal.innerHornFillers_op hD
  let ψ := reverseHornMap (k + 2) (0 : Fin (k + 3)) φ
  let γ := reverseBaseMap (k + 2) β
  have hψ : ψ ≫ SSet.opFunctor.map p =
      Λ[k + 2, (0 : Fin (k + 3)).rev].ι ≫ γ :=
    reverse_square p (k + 2) 0 φ β w
  have heRev : edgeIsInvertible C.op
      (SSet.yonedaEquiv (rightEdgeAtReversedIndex k ≫ ψ)) := by
    dsimp only [ψ]
    rw [reversed_edge_image, yoneda_reversed_edge]
    exact edgeIsInvertible_op C _ he
  have hrightGeneral :
      ∀ (ψ' : (Λ[k + 2, (0 : Fin (k + 3)).rev] : SSet.{u}) ⟶ C.op)
        (γ' : (Δ[k + 2] : SSet.{u}) ⟶ D.op),
        ψ' ≫ SSet.opFunctor.map p =
          Λ[k + 2, (0 : Fin (k + 3)).rev].ι ≫ γ' →
        edgeIsInvertible C.op
          (SSet.yonedaEquiv (rightEdgeAtReversedIndex k ≫ ψ')) →
        ∃ τ : (Δ[k + 2] : SSet.{u}) ⟶ C.op,
          ψ' = Λ[k + 2, (0 : Fin (k + 3)).rev].ι ≫ τ ∧
            τ ≫ SSet.opFunctor.map p = γ' := by
    simpa only [rightEdgeAtReversedIndex,
      show (0 : Fin (k + 3)).rev = Fin.last (k + 2) by
        apply Fin.ext
        simp only [Fin.val_rev, Fin.val_zero, Fin.val_last]
        omega] using
      (fun (ψ' : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ C.op)
        (γ' : (Δ[k + 2] : SSet.{u}) ⟶ D.op)
        (hψ' : ψ' ≫ SSet.opFunctor.map p =
          Λ[k + 2, Fin.last (k + 2)].ι ≫ γ')
        (he' : edgeIsInvertible C.op
          (SSet.yonedaEquiv
            (DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion k ≫
              ψ'))) =>
        right_outer_horn_filler_over
          (SSet.opFunctor.map p) hpOp hCOp hDOp k ψ' γ' hψ' he')
  have hright : ∃ τ : (Δ[k + 2] : SSet.{u}) ⟶ C.op,
      ψ = Λ[k + 2, (0 : Fin (k + 3)).rev].ι ≫ τ ∧
        τ ≫ SSet.opFunctor.map p = γ :=
    hrightGeneral ψ γ hψ heRev
  obtain ⟨τ, hτ, hbase⟩ := hright
  exact relative_extension_of_reversed_extension p (k + 2) 0 φ β τ hτ hbase

#print axioms selected_left_outer_horn_filler_over

end

end DaggerModels.PartII.RelativeSelectedLeftOuterHornFilling
