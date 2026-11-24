import NativeSimplicialReplacementWeightsChange

/-!
# Whole-coefficient sections of the original full replacement

The section retains the entire coefficient simplex on the constant chain.
Its exact change-of-weights and augmentation identities are used to compare
the original component maps with their original whole-bar counterparts.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplicialReplacementWeightsChange

universe u

namespace DaggerModels.PartII.ReplacementConstantSections

noncomputable section

variable {C : Type u} [Category.{u} C]

private def constantChain (c : C) (q : SimplexCategoryᵒᵖ) : Chain (C := C) q :=
  (Functor.const (Fin (q.unop.len + 1))).obj c

/-- Reinsert the SAME entire coefficient on the constant chain at c. -/
def sectionMap (G : C ⥤ SSet.{u}) (c : C) :
    G.obj c ⟶ DaggerBisimplicialDiagonal.diag (replacement G) where
  app q x := ⟨constantChain c q, x⟩
  naturality {q r} β := by
    funext x
    change (⟨constantChain c r, (G.obj c).map β x⟩ : Cell G r r) =
      (DaggerBisimplicialDiagonal.diag (replacement G)).map β ⟨constantChain c q, x⟩
    rw [DaggerBisimplicialDiagonal.diag_map_other_order]
    change (⟨constantChain c r, (G.obj c).map β x⟩ : Cell G r r) =
      ⟨(nerve C).map β (constantChain c q),
        (G.map (initialArrow β (constantChain c q))).app r ((G.obj c).map β x)⟩
    have hc : (nerve C).map β (constantChain c q) = constantChain c r := by
      refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
      intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    have hi : initialArrow β (constantChain c q) = 𝟙 c := rfl
    have hm : G.map (𝟙 c) = 𝟙 (G.obj c) := G.map_id c
    rw [hi, hm]
    exact Sigma.ext hc.symm HEq.rfl

/-- The original whole-bar weight map restricts to its SAME component map. -/
theorem section_change {G H : C ⥤ SSet.{u}} (η : G ⟶ H) (c : C) :
    sectionMap G c ≫ diagonalChange η = η.app c ≫ sectionMap H c := by
  apply NatTrans.ext
  rfl

/-- The original whole-bar augmentation restricts to its SAME cocone leg. -/
theorem section_augmentation (G : C ⥤ SSet.{u}) {X : SSet.{u}}
    (η : G ⟶ (Functor.const C).obj X) (c : C) :
    sectionMap G c ≫ diagonalAugmentation G η = η.app c := by
  apply NatTrans.ext
  rfl

/-- Every original full-diagonal augmentation commutes with postcomposition. -/
theorem augmentation_postcompose (G : C ⥤ SSet.{u}) {X Y : SSet.{u}}
    (η : G ⟶ (Functor.const C).obj X) (f : X ⟶ Y) :
    diagonalAugmentation G η ≫ f =
      diagonalAugmentation G (η ≫ (Functor.const C).map f) := by
  apply NatTrans.ext
  rfl

end

end DaggerModels.PartII.ReplacementConstantSections
