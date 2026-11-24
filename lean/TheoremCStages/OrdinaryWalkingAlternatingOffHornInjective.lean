import OrdinaryWalkingAlternatingIntersection

/-!
# Injectivity of the alternating attachment away from the outer horn

An operator outside the zero outer horn is epi onto the top simplex or epi
onto its zero face. Both resulting binary words are nondegenerate and have
different dimensions. Uniqueness of nondegenerate degeneracy decompositions
therefore identifies operators with equal images away from the horn.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingAlternatingOffHornInjective

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

private theorem zeroFace_decomp (k m : ℕ)
    (α : ⦋m⦌ ⟶ ⦋k + 2⦌) (σ : ⦋m⦌ ⟶ ⦋k + 1⦌)
    (hσ : σ ≫ SimplexCategory.δ (0 : Fin (k + 3)) = α) :
    BinaryNerve.map α.op (binaryWord (k + 2)) =
      BinaryNerve.map σ.op
        (BinaryNerve.map (SimplexCategory.δ (0 : Fin (k + 3))).op
          (binaryWord (k + 2))) := by
  rw [← hσ, op_comp, FunctorToTypes.map_comp_apply]

/-- The literal simplex map is injective between simplices outside the
missing-zero outer horn, despite failing to be a global monomorphism. -/
theorem attachmentMap_injective_off_horn (k m : ℕ)
    (s t : (Δ[k + 2] : SSet).obj (op ⦋m⦌))
    (hs : s ∉ (SSet.horn (k + 2) (0 : Fin (k + 3))).obj (op ⦋m⦌))
    (ht : t ∉ (SSet.horn (k + 2) (0 : Fin (k + 3))).obj (op ⦋m⦌))
    (heq : (attachmentMap (k + 2)).app (op ⦋m⦌) s =
      (attachmentMap (k + 2)).app (op ⦋m⦌) t) : s = t := by
  let α : ⦋m⦌ ⟶ ⦋k + 2⦌ := SSet.stdSimplex.objEquiv s
  let β : ⦋m⦌ ⟶ ⦋k + 2⦌ := SSet.stdSimplex.objEquiv t
  have hα := congrFun (walkingCodiscreteIso.hom.naturality α.op)
    (alternatingSimplex (k + 2))
  have hβ := congrFun (walkingCodiscreteIso.hom.naturality β.op)
    (alternatingSimplex (k + 2))
  change BinaryNerve.map α.op
      (walkingCodiscreteIso.hom.app (op ⦋k + 2⦌)
        (alternatingSimplex (k + 2))) =
    walkingCodiscreteIso.hom.app (op ⦋m⦌)
      (Walking.map α.op (alternatingSimplex (k + 2))) at hα
  change BinaryNerve.map β.op
      (walkingCodiscreteIso.hom.app (op ⦋k + 2⦌)
        (alternatingSimplex (k + 2))) =
    walkingCodiscreteIso.hom.app (op ⦋m⦌)
      (Walking.map β.op (alternatingSimplex (k + 2))) at hβ
  rw [binary_of_alternating] at hα hβ
  have hcomparison := congrArg (walkingCodiscreteIso.hom.app (op ⦋m⦌)) heq
  change walkingCodiscreteIso.hom.app (op ⦋m⦌)
      (Walking.map α.op (alternatingSimplex (k + 2))) =
    walkingCodiscreteIso.hom.app (op ⦋m⦌)
      (Walking.map β.op (alternatingSimplex (k + 2))) at hcomparison
  let x : BinaryNerve.obj (op ⦋m⦌) :=
    BinaryNerve.map α.op (binaryWord (k + 2))
  have hword : x = BinaryNerve.map β.op (binaryWord (k + 2)) :=
    hα.trans (hcomparison.trans hβ.symm)
  have hαcases : Epi α ∨
      ∃ σ : ⦋m⦌ ⟶ ⦋k + 1⦌, Epi σ ∧
        σ ≫ SimplexCategory.δ (0 : Fin (k + 3)) = α :=
    outside_horn_epi_or_zero_face k m s hs
  have hβcases : Epi β ∨
      ∃ τ : ⦋m⦌ ⟶ ⦋k + 1⦌, Epi τ ∧
        τ ≫ SimplexCategory.δ (0 : Fin (k + 3)) = β :=
    outside_horn_epi_or_zero_face k m t ht
  rcases hαcases with hαepi | ⟨σ, hσepi, hσfac⟩
  · letI : Epi α := hαepi
    rcases hβcases with hβepi | ⟨τ, hτepi, hτfac⟩
    · letI : Epi β := hβepi
      have hoperators := BinaryNerve.unique_nonDegenerate_map x α
        ⟨binaryWord (k + 2), binaryWord_nonDegenerate (k + 2)⟩ rfl
        β ⟨binaryWord (k + 2), binaryWord_nonDegenerate (k + 2)⟩ hword
      exact SSet.stdSimplex.objEquiv.injective hoperators
    · letI : Epi τ := hτepi
      have hτmap : x = BinaryNerve.map τ.op
          (BinaryNerve.map (SimplexCategory.δ (0 : Fin (k + 3))).op
            (binaryWord (k + 2))) :=
        hword.trans (zeroFace_decomp k m β τ hτfac)
      have hdim := BinaryNerve.unique_nonDegenerate_dim x α
        ⟨binaryWord (k + 2), binaryWord_nonDegenerate (k + 2)⟩ rfl
        τ ⟨_, binaryWord_zeroFace_nonDegenerate k⟩ hτmap
      omega
  · letI : Epi σ := hσepi
    have hσmap : x = BinaryNerve.map σ.op
        (BinaryNerve.map (SimplexCategory.δ (0 : Fin (k + 3))).op
          (binaryWord (k + 2))) :=
      zeroFace_decomp k m α σ hσfac
    rcases hβcases with hβepi | ⟨τ, hτepi, hτfac⟩
    · letI : Epi β := hβepi
      have hdim := BinaryNerve.unique_nonDegenerate_dim x σ
        ⟨_, binaryWord_zeroFace_nonDegenerate k⟩ hσmap
        β ⟨binaryWord (k + 2), binaryWord_nonDegenerate (k + 2)⟩ hword
      omega
    · letI : Epi τ := hτepi
      have hτmap : x = BinaryNerve.map τ.op
          (BinaryNerve.map (SimplexCategory.δ (0 : Fin (k + 3))).op
            (binaryWord (k + 2))) :=
        hword.trans (zeroFace_decomp k m β τ hτfac)
      have hoperators := BinaryNerve.unique_nonDegenerate_map x σ
        ⟨_, binaryWord_zeroFace_nonDegenerate k⟩ hσmap
        τ ⟨_, binaryWord_zeroFace_nonDegenerate k⟩ hτmap
      apply SSet.stdSimplex.objEquiv.injective
      change α = β
      rw [← hσfac, ← hτfac, hoperators]

#print axioms attachmentMap_injective_off_horn

end

end DaggerModels.PartII.OrdinaryWalkingAlternatingOffHornInjective
