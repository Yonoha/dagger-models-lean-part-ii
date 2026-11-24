import RelativeHornFillingReversal

/-!
# Transport one specified relative horn filler through reversal

This strengthens the global right-lifting-class equivalence when only one
selected reversed square has a filler. The given reversed filler `τ` is
transported through the actual double-opposite isomorphism, and both the
original horn restriction and prescribed base map are verified. No lifting
property for all horns is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerOriginalStandardSimplexReversal DaggerOriginalHornReversal
open DaggerOriginalHornFillingReversal
open DaggerModels.PartII.RelativeHornFillingReversal

universe u

namespace DaggerModels.PartII.RelativeHornReversedExtension

noncomputable section

/-- One selected reversed relative filler returns a filler of the exact
original square, including its specified base map. -/
theorem relative_extension_of_reversed_extension {X Y : SSet.{u}}
    (p : X ⟶ Y) (n : ℕ) (i : Fin (n + 1))
    (φ : (Λ[n, i] : SSet.{u}) ⟶ X)
    (β : (Δ[n] : SSet.{u}) ⟶ Y)
    (τ : (Δ[n] : SSet.{u}) ⟶ X.op)
    (hτ : reverseHornMap n i φ = Λ[n, i.rev].ι ≫ τ)
    (hbase : τ ≫ SSet.opFunctor.map p = reverseBaseMap n β) :
    ∃ σ : (Δ[n] : SSet.{u}) ⟶ X,
      φ = Λ[n, i].ι ≫ σ ∧ σ ≫ p = β := by
  let ε := SSet.opFunctorCompOpFunctorIso.{u}
  let σ : (Δ[n] : SSet.{u}) ⟶ X :=
    ε.inv.app Δ[n] ≫
      SSet.opFunctor.map (standardSimplexReversalHom n) ≫
        SSet.opFunctor.map τ ≫ ε.hom.app X
  have hhi : hornReversalHom.{u} n i ≫ hornReversalInv n i = 𝟙 _ :=
    (hornReversalIso n i).hom_inv_id
  have hh := congrArg (fun f ↦ hornReversalHom n i ≫ f) hτ
  change hornReversalHom n i ≫
      (hornReversalInv n i ≫ SSet.opFunctor.map φ) =
    hornReversalHom n i ≫ (Λ[n, i.rev].ι ≫ τ) at hh
  rw [← Category.assoc, hhi, Category.id_comp, ← Category.assoc,
    hornReversalHom_comp_ι, Category.assoc] at hh
  have ho := congrArg SSet.opFunctor.map hh
  simp only [Functor.map_comp] at ho
  have hn := ε.inv.naturality (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι
  change Λ[n, i].ι ≫ ε.inv.app Δ[n] =
    ε.inv.app (Λ[n, i] : SSet.{u}) ≫
      SSet.opFunctor.map (SSet.opFunctor.map Λ[n, i].ι) at hn
  have hf := ε.hom.naturality φ
  change SSet.opFunctor.map (SSet.opFunctor.map φ) ≫ ε.hom.app X =
    ε.hom.app (Λ[n, i] : SSet.{u}) ≫ φ at hf
  have hc : ε.inv.app (Λ[n, i] : SSet.{u}) ≫
      ε.hom.app (Λ[n, i] : SSet.{u}) = 𝟙 _ := (ε.app _).inv_hom_id
  have hhorn : φ = Λ[n, i].ι ≫ σ := by
    calc
      φ = ε.inv.app (Λ[n, i] : SSet.{u}) ≫
          (SSet.opFunctor.map (SSet.opFunctor.map φ) ≫ ε.hom.app X) := by
        rw [hf, ← Category.assoc, hc, Category.id_comp]
      _ = ε.inv.app (Λ[n, i] : SSet.{u}) ≫
          (SSet.opFunctor.map (SSet.opFunctor.map Λ[n, i].ι) ≫
            (SSet.opFunctor.map (standardSimplexReversalHom n) ≫
              (SSet.opFunctor.map τ ≫ ε.hom.app X))) := by
        rw [ho]
        simp only [Category.assoc]
      _ = Λ[n, i].ι ≫ σ := by
        dsimp only [σ]
        simp only [← Category.assoc]
        rw [hn]
  have hpNat := ε.hom.naturality p
  change SSet.opFunctor.map (SSet.opFunctor.map p) ≫ ε.hom.app Y =
    ε.hom.app X ≫ p at hpNat
  have hbNat := ε.inv.naturality β
  change β ≫ ε.inv.app Y = ε.inv.app Δ[n] ≫
    SSet.opFunctor.map (SSet.opFunctor.map β) at hbNat
  have hcancel : SSet.opFunctor.map (standardSimplexReversalHom n) ≫
      SSet.opFunctor.map (standardSimplexReversalInv n) = 𝟙 _ := by
    have h : standardSimplexReversalHom n ≫ standardSimplexReversalInv n = 𝟙 _ :=
      (standardSimplexReversalIso n).hom_inv_id
    rw [← Functor.map_comp, h, SSet.opFunctor.map_id]
  have hbaseOriginal : σ ≫ p = β := by
    calc
      σ ≫ p = ε.inv.app Δ[n] ≫
          SSet.opFunctor.map (standardSimplexReversalHom n) ≫
            SSet.opFunctor.map τ ≫
              (SSet.opFunctor.map (SSet.opFunctor.map p) ≫ ε.hom.app Y) := by
        dsimp only [σ]
        simp only [Category.assoc, hpNat]
      _ = ε.inv.app Δ[n] ≫
          SSet.opFunctor.map (standardSimplexReversalHom n) ≫
            SSet.opFunctor.map (τ ≫ SSet.opFunctor.map p) ≫
              ε.hom.app Y := by
        simp only [Functor.map_comp, Category.assoc]
      _ = ε.inv.app Δ[n] ≫
          SSet.opFunctor.map (standardSimplexReversalHom n) ≫
            SSet.opFunctor.map (reverseBaseMap n β) ≫
              ε.hom.app Y := by rw [hbase]
      _ = ε.inv.app Δ[n] ≫
          SSet.opFunctor.map (SSet.opFunctor.map β) ≫ ε.hom.app Y := by
        dsimp only [reverseBaseMap]
        simp only [Functor.map_comp, Category.assoc]
        have hc' := congrArg
          (fun t ↦ ε.inv.app Δ[n] ≫ t ≫
            (SSet.opFunctor.map (SSet.opFunctor.map β) ≫ ε.hom.app Y)) hcancel
        simpa only [Category.assoc, Category.id_comp] using hc' 
      _ = β := by
        calc
          _ = (β ≫ ε.inv.app Y) ≫ ε.hom.app Y := by
            exact (congrArg (fun t ↦ t ≫ ε.hom.app Y) hbNat).symm
          _ = β := by
            have hcY : ε.inv.app Y ≫ ε.hom.app Y = 𝟙 Y := (ε.app Y).inv_hom_id
            rw [Category.assoc, hcY, Category.comp_id]
  exact ⟨σ, hhorn, hbaseOriginal⟩

#print axioms relative_extension_of_reversed_extension

end

end DaggerModels.PartII.RelativeHornReversedExtension
