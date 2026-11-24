import DaggerModelsPartII.ReversalRepresentableFixedPoints
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Yoneda

/-!
# The two outer faces of a reversal representable

The set-valued reversal representable is the actual Yoneda presheaf on
`DaggerModels.ReverseSimplex`. Its outer-face subpresheaf is the union of the
images of the two outer cofaces. The fixed-point calculation places every
fixed element in this union in positive even target length.
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace DaggerModels.PartII.ReversalOuterFaceSubobject

open ReverseSimplex ReversalRepresentableFixedPoints

/-- The coface omitting the initial vertex of a reversal simplex. -/
def firstOuterCoface (t : ℕ) :
    (⟨t⟩ : ReverseSimplex) ⟶ ⟨t + 1⟩ where
  toFun i := i.succ
  monotone_or_antitone := Or.inl (fun _ _ h ↦ Fin.succ_le_succ_iff.mpr h)

/-- The coface omitting the final vertex of a reversal simplex. -/
def lastOuterCoface (t : ℕ) :
    (⟨t⟩ : ReverseSimplex) ⟶ ⟨t + 1⟩ where
  toFun i := i.castSucc
  monotone_or_antitone := Or.inl (fun _ _ h ↦ Fin.castSucc_le_castSucc_iff.mpr h)

/-- The first outer coface is exactly the ordinary simplicial coface `δ₀`
included in the actual reversal category. -/
theorem firstOuterCoface_eq_delta (t : ℕ) :
    firstOuterCoface t =
      inclusion.map (SimplexCategory.δ (0 : Fin (t + 2))) := by
  apply Hom.ext
  intro i
  rfl

/-- The last outer coface is exactly the ordinary final simplicial coface
included in the actual reversal category. -/
theorem lastOuterCoface_eq_delta (t : ℕ) :
    lastOuterCoface t =
      inclusion.map (SimplexCategory.δ (Fin.last (t + 1))) := by
  apply Hom.ext
  intro i
  change i.castSucc = (Fin.last (t + 1)).succAbove i
  exact (Fin.succAbove_last_apply i).symm

/-- The literal union of the Yoneda images of the two outer cofaces. -/
def outerFaceSubpresheaf (t : ℕ) :
    Subfunctor (yoneda.obj (⟨t + 1⟩ : ReverseSimplex)) :=
  Subfunctor.range (yoneda.map (firstOuterCoface t)) ⊔
    Subfunctor.range (yoneda.map (lastOuterCoface t))

/-- The same subpresheaf indexed by its positive target length, as in the
manuscript's notation `A_rev^ℓ`. -/
def outerFaceSubpresheafAt (l : ℕ) (hl : 1 ≤ l) :
    Subfunctor (yoneda.obj (⟨l⟩ : ReverseSimplex)) := by
  have hlen : (l - 1) + 1 = l := by omega
  simpa only [hlen] using outerFaceSubpresheaf (l - 1)

/-- Any actual reversal map omitting the final vertex factors through the
last outer coface. -/
def factorThroughLast {k : ReverseSimplex} {t : ℕ}
    (f : k ⟶ (⟨t + 1⟩ : ReverseSimplex))
    (h : ∀ i : Fin (k.len + 1), (f.toFun i).val < t + 1) :
    k ⟶ (⟨t⟩ : ReverseSimplex) where
  toFun i := ⟨(f.toFun i).val, h i⟩
  monotone_or_antitone := by
    rcases f.monotone_or_antitone with hf | hf
    · exact Or.inl (fun i j hij ↦ hf hij)
    · exact Or.inr (fun i j hij ↦ hf hij)

theorem factorThroughLast_comp {k : ReverseSimplex} {t : ℕ}
    (f : k ⟶ (⟨t + 1⟩ : ReverseSimplex))
    (h : ∀ i : Fin (k.len + 1), (f.toFun i).val < t + 1) :
    factorThroughLast f h ≫ lastOuterCoface t = f := by
  apply Hom.ext
  intro i
  apply Fin.ext
  rfl

/-- Omitting the final vertex is a sufficient membership criterion for the
literal union of outer-face images. -/
theorem mem_outerFaceSubpresheaf_of_omits_last {k : ReverseSimplex} {t : ℕ}
    (f : k ⟶ (⟨t + 1⟩ : ReverseSimplex))
    (h : ∀ i : Fin (k.len + 1), (f.toFun i).val < t + 1) :
    f ∈ (outerFaceSubpresheaf t).obj (op k) := by
  apply Or.inr
  refine ⟨factorThroughLast f h, ?_⟩
  exact factorThroughLast_comp f h

/-- For positive even length, every fixed actual representable element lies
in the outer-face union. The target length `2*r+2` covers all positive even
lengths. -/
theorem fixed_mem_outerFaceSubpresheaf (k r : ℕ)
    (f : (⟨k⟩ : ReverseSimplex) ⟶ ⟨2 * r + 2⟩) (hf : flip f = f) :
    f ∈ (outerFaceSubpresheaf (2 * r + 1)).obj (op (⟨k⟩ : ReverseSimplex)) := by
  apply mem_outerFaceSubpresheaf_of_omits_last
  intro i
  have hv := (rev_fixed_iff_twice_val (f.toFun i)).mp ((flip_fixed_iff f).mp hf i)
  change 2 * (f.toFun i).val = 2 * r + 2 at hv
  omega

/-- In manuscript indexing, fixed representable elements of any positive
even length belong to `A_rev^ℓ`. -/
theorem fixed_mem_outerFaceSubpresheafAt (k l : ℕ)
    (hl : 2 ≤ l) (he : Even l)
    (f : (⟨k⟩ : ReverseSimplex) ⟶ ⟨l⟩) (hf : flip f = f) :
    f ∈ (outerFaceSubpresheafAt l (by omega)).obj
      (op (⟨k⟩ : ReverseSimplex)) := by
  obtain ⟨s, hs⟩ := even_iff_exists_two_mul.mp he
  have hsone : 1 ≤ s := by omega
  let r := s - 1
  have hlen : l = 2 * r + 2 := by omega
  clear hs
  subst l
  have h : f ∈ (outerFaceSubpresheaf (2 * r + 1)).obj
      (op (⟨k⟩ : ReverseSimplex)) := fixed_mem_outerFaceSubpresheaf k r f hf
  simpa only [outerFaceSubpresheafAt, show 2 * r + 2 - 1 = 2 * r + 1 by omega]
    using h

end DaggerModels.PartII.ReversalOuterFaceSubobject
