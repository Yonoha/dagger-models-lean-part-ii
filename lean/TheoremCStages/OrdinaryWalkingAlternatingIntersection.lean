import OrdinaryWalkingAlternatingOutsideHorn
import OrdinaryWalkingAlternatingNondegenerate
import TopCatModelCategory.SSet.Simplices

/-!
# Exact outer-horn intersection with the preceding alternating stage

An operator outside the zero outer horn is epi onto the top simplex or onto
its zero face. Epi degeneracies generate the same subcomplex as their source
simplex. The two source simplices are not in the preceding alternating stage,
so the actual preimage of that stage is exactly the zero outer horn.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingAlternatingIntersection

open OrdinaryWalkingAlternatingFiltration
open OrdinaryWalkingAlternatingAttachment
open OrdinaryWalkingAlternatingOutsideHorn
open OrdinaryWalkingAlternatingNondegenerate

noncomputable section

private abbrev Walking := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev BinaryNerve :=
  DaggerOriginalCodiscreteNerveInjective.codiscreteNerve.obj (Fin 2)

private theorem binary_of_alternating (n : ℕ) :
    walkingCodiscreteIso.hom.app (op ⦋n⦌) (alternatingSimplex n) =
      binaryWord n := by
  have h := congrFun (NatTrans.congr_app walkingCodiscreteIso.inv_hom_id
    (op ⦋n⦌)) (binaryWord n)
  change walkingCodiscreteIso.hom.app (op ⦋n⦌)
      (walkingCodiscreteIso.inv.app (op ⦋n⦌) (binaryWord n)) =
    binaryWord n at h
  exact h

/-- Membership in a literal stage implies membership in the generated
binary stage after the checked codiscrete comparison. -/
private theorem binary_mem_of_stage (n m : ℕ)
    (x : Walking.obj (op ⦋m⦌))
    (hx : x ∈ (stage n).obj (op ⦋m⦌)) :
    walkingCodiscreteIso.hom.app (op ⦋m⦌) x ∈
      (SSet.Subcomplex.ofSimplex (binaryWord n)).obj (op ⦋m⦌) := by
  rw [stage, SSet.Subcomplex.mem_ofSimplex_obj_iff] at hx
  obtain ⟨f, hf⟩ := hx
  rw [SSet.Subcomplex.mem_ofSimplex_obj_iff]
  refine ⟨f, ?_⟩
  have h := congrFun (walkingCodiscreteIso.hom.naturality f.op)
    (alternatingSimplex n)
  change BinaryNerve.map f.op
      (walkingCodiscreteIso.hom.app (op ⦋n⦌) (alternatingSimplex n)) =
    walkingCodiscreteIso.hom.app (op ⦋m⦌)
      (Walking.map f.op (alternatingSimplex n)) at h
  rw [binary_of_alternating, hf] at h
  exact h

/-- The preimage of the preceding stage under the actual alternating
simplex map has no simplex outside the zero outer horn. -/
theorem preimage_le_horn (k : ℕ) :
    (stage (k + 1)).preimage (attachmentMap (k + 2)) ≤
      SSet.horn (k + 2) (0 : Fin (k + 3)) := by
  intro q s hs
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = op ⦋m⦌ :=
    ⟨q.unop.len, by simp only [SimplexCategory.mk_len, op_unop]⟩
  by_contra hnot
  have hcases := outside_horn_epi_or_zero_face k m s hnot
  change Walking.map (SSet.stdSimplex.objEquiv s).op
      (alternatingSimplex (k + 2)) ∈
    (stage (k + 1)).obj (op ⦋m⦌) at hs
  have hb := binary_mem_of_stage (k + 1) m _ hs
  have hnat := congrFun (walkingCodiscreteIso.hom.naturality
    (SSet.stdSimplex.objEquiv s).op) (alternatingSimplex (k + 2))
  change BinaryNerve.map (SSet.stdSimplex.objEquiv s).op
      (walkingCodiscreteIso.hom.app (op ⦋k + 2⦌)
        (alternatingSimplex (k + 2))) =
    walkingCodiscreteIso.hom.app (op ⦋m⦌)
      (Walking.map (SSet.stdSimplex.objEquiv s).op
        (alternatingSimplex (k + 2))) at hnat
  rw [binary_of_alternating] at hnat
  rw [← hnat] at hb
  rcases hcases with hfull | ⟨β, hβ, hfac⟩
  · letI : Epi (SSet.stdSimplex.objEquiv s) := hfull
    have hsub : SSet.Subcomplex.ofSimplex
        (BinaryNerve.map (SSet.stdSimplex.objEquiv s).op
          (binaryWord (k + 2))) ≤
        SSet.Subcomplex.ofSimplex (binaryWord (k + 1)) :=
      (SSet.Subcomplex.ofSimplex_le_iff _ _).mpr hb
    rw [SSet.Subcomplex.ofSimplex_map] at hsub
    exact binaryWord_top_not_previous k
      (hsub _ (SSet.Subcomplex.mem_ofSimplex_obj _))
  · haveI : Epi β := hβ
    rw [← hfac, op_comp, FunctorToTypes.map_comp_apply] at hb
    have hsub : SSet.Subcomplex.ofSimplex
        (BinaryNerve.map β.op
          (BinaryNerve.map (SimplexCategory.δ (0 : Fin (k + 3))).op
            (binaryWord (k + 2)))) ≤
        SSet.Subcomplex.ofSimplex (binaryWord (k + 1)) :=
      (SSet.Subcomplex.ofSimplex_le_iff _ _).mpr hb
    rw [SSet.Subcomplex.ofSimplex_map] at hsub
    exact binaryWord_zeroFace_not_previous k
      (hsub _ (SSet.Subcomplex.mem_ofSimplex_obj _))

/-- The actual intersection of the new simplex with the previous stage is
exactly the missing-zero outer horn. -/
theorem preimage_eq_horn (k : ℕ) :
    (stage (k + 1)).preimage (attachmentMap (k + 2)) =
      SSet.horn (k + 2) (0 : Fin (k + 3)) :=
  le_antisymm (preimage_le_horn k) (horn_le_preimage k)

#print axioms preimage_le_horn
#print axioms preimage_eq_horn

end

end DaggerModels.PartII.OrdinaryWalkingAlternatingIntersection
