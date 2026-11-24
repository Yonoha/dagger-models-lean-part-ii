import DaggerModelsPartII.ReversalOuterFaceSubobject
import DaggerModelsPartII.DiscreteBorelDiagram

/-!
# Reversal action on an outer-face subpresheaf

The actual representable of the reversal simplex carries its postcomposition
involution. The union of its two outer faces is invariant, and contains every
fixed point in target length at least two.
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace DaggerModels.PartII.ReversalOuterFaceAction

open ReverseSimplex ReversalRepresentableFixedPoints
open ReversalOuterFaceSubobject DiscreteBorelDiagram

/-- Postcomposition with the actual ordinal reversal on the Yoneda representable. -/
def representableReversalIso (l : ℕ) :
    yoneda.obj (⟨l⟩ : ReverseSimplex) ≅ yoneda.obj (⟨l⟩ : ReverseSimplex) where
  hom := yoneda.map (reversal (⟨l⟩ : ReverseSimplex))
  inv := yoneda.map (reversal (⟨l⟩ : ReverseSimplex))
  hom_inv_id := by
    rw [← yoneda.map_comp, reversal_comp_reversal, yoneda.map_id]
  inv_hom_id := by
    rw [← yoneda.map_comp, reversal_comp_reversal, yoneda.map_id]

/-- The representable reversal squares to the identity. -/
theorem representableReversal_involutive (l : ℕ) :
    (representableReversalIso l).hom ≫ (representableReversalIso l).hom =
      𝟙 (yoneda.obj (⟨l⟩ : ReverseSimplex)) := by
  change (representableReversalIso l).hom ≫ (representableReversalIso l).inv = _
  exact (representableReversalIso l).hom_inv_id

/-- Reversal sends the first outer coface to the last outer coface. -/
theorem firstOuterCoface_reversal (t : ℕ) :
    firstOuterCoface t ≫ reversal (⟨t + 1⟩ : ReverseSimplex) =
      reversal (⟨t⟩ : ReverseSimplex) ≫ lastOuterCoface t := by
  apply Hom.ext
  intro i
  apply Fin.ext
  change ((i.succ).rev).val = ((i.rev).castSucc).val
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega

/-- Reversal sends the last outer coface to the first outer coface. -/
theorem lastOuterCoface_reversal (t : ℕ) :
    lastOuterCoface t ≫ reversal (⟨t + 1⟩ : ReverseSimplex) =
      reversal (⟨t⟩ : ReverseSimplex) ≫ firstOuterCoface t := by
  apply Hom.ext
  intro i
  apply Fin.ext
  change ((i.castSucc).rev).val = ((i.rev).succ).val
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega

/-- Postcomposition with reversal interchanges the two outer-face images. -/
theorem flip_mem_outerFaceSubpresheaf (t : ℕ) {k : ReverseSimplex}
    (f : k ⟶ (⟨t + 1⟩ : ReverseSimplex))
    (hf : f ∈ (outerFaceSubpresheaf t).obj (op k)) :
    flip f ∈ (outerFaceSubpresheaf t).obj (op k) := by
  rcases hf with ⟨g, hg⟩ | ⟨g, hg⟩
  · apply Or.inr
    change g ≫ firstOuterCoface t = f at hg
    refine ⟨g ≫ reversal (⟨t⟩ : ReverseSimplex), ?_⟩
    change (g ≫ reversal (⟨t⟩ : ReverseSimplex)) ≫ lastOuterCoface t =
      f ≫ reversal (⟨t + 1⟩ : ReverseSimplex)
    calc
      (g ≫ reversal (⟨t⟩ : ReverseSimplex)) ≫ lastOuterCoface t =
          g ≫ (reversal (⟨t⟩ : ReverseSimplex) ≫ lastOuterCoface t) :=
        Category.assoc _ _ _
      _ = g ≫ (firstOuterCoface t ≫ reversal (⟨t + 1⟩ : ReverseSimplex)) := by
        rw [firstOuterCoface_reversal]
      _ = (g ≫ firstOuterCoface t) ≫ reversal (⟨t + 1⟩ : ReverseSimplex) :=
        (Category.assoc _ _ _).symm
      _ = f ≫ reversal (⟨t + 1⟩ : ReverseSimplex) := by rw [hg]
  · apply Or.inl
    change g ≫ lastOuterCoface t = f at hg
    refine ⟨g ≫ reversal (⟨t⟩ : ReverseSimplex), ?_⟩
    change (g ≫ reversal (⟨t⟩ : ReverseSimplex)) ≫ firstOuterCoface t =
      f ≫ reversal (⟨t + 1⟩ : ReverseSimplex)
    calc
      (g ≫ reversal (⟨t⟩ : ReverseSimplex)) ≫ firstOuterCoface t =
          g ≫ (reversal (⟨t⟩ : ReverseSimplex) ≫ firstOuterCoface t) :=
        Category.assoc _ _ _
      _ = g ≫ (lastOuterCoface t ≫ reversal (⟨t + 1⟩ : ReverseSimplex)) := by
        rw [lastOuterCoface_reversal]
      _ = (g ≫ lastOuterCoface t) ≫ reversal (⟨t + 1⟩ : ReverseSimplex) :=
        (Category.assoc _ _ _).symm
      _ = f ≫ reversal (⟨t + 1⟩ : ReverseSimplex) := by rw [hg]

/-- The outer-face subpresheaf is invariant under the actual Yoneda reversal. -/
theorem outerFace_invariant (l : ℕ) (hl : 1 ≤ l) :
    ∀ c x, x ∈ (outerFaceSubpresheafAt l hl).obj c →
      valueEquiv (yoneda.obj (⟨l⟩ : ReverseSimplex))
        (representableReversalIso l) c x ∈
          (outerFaceSubpresheafAt l hl).obj c := by
  intro c x hx
  cases l with
  | zero => omega
  | succ t =>
    have hface : x ∈ (outerFaceSubpresheaf t).obj c := by
      simpa [outerFaceSubpresheafAt] using hx
    have hflip := flip_mem_outerFaceSubpresheaf t x hface
    change flip x ∈ (outerFaceSubpresheafAt (t + 1) hl).obj c
    simpa [outerFaceSubpresheafAt] using hflip

/-- Every fixed representable element in target length at least two belongs
to the outer-face subpresheaf. -/
theorem outerFace_fixed (l : ℕ) (hl : 2 ≤ l) :
    ∀ c x,
      valueEquiv (yoneda.obj (⟨l⟩ : ReverseSimplex))
        (representableReversalIso l) c x = x →
        x ∈ (outerFaceSubpresheafAt l (by omega)).obj c := by
  intro c x hx
  cases l with
  | zero => omega
  | succ t =>
    have hlen : 2 ≤ t + 1 := hl
    have hfixed : flip x = x := hx
    have homits : ∀ i : Fin (c.unop.len + 1), (x.toFun i).val < t + 1 := by
      intro i
      have hv := (rev_fixed_iff_twice_val (x.toFun i)).mp
        ((flip_fixed_iff x).mp hfixed i)
      change 2 * (x.toFun i).val = t + 1 at hv
      omega
    have hface := mem_outerFaceSubpresheaf_of_omits_last x homits
    simpa [outerFaceSubpresheafAt] using hface

end DaggerModels.PartII.ReversalOuterFaceAction
