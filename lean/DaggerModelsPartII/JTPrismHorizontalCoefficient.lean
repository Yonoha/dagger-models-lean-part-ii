import DaggerModelsPartII.JTPrismCoefficientRigidity

/-! The full prism realization retains its coefficient under horizontal split descent. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTPrismRectangle

open OrdinaryJTRealization JTRealizationGenerators JTRowGraphRelations JTRowGraphParameterSupport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev prism (d t : SimplexCategory) := std.obj d ⊗ J.obj t

variable {W : BiPresheaf} {d e t k l : SimplexCategory}

/-- Realize the coefficient over the whole product with time. -/
def prismValue (w : W.obj (op (d, k))) (p : prism d t ⟶ J.obj k) :
    prism d t ⟶ realization.obj W :=
  lift (fst (std.obj d) (J.obj t)) p ≫ generator W (d, k) w

/-- The full product realization commutes with both coefficient operators. -/
theorem prismValue_pullback (a : d ⟶ e) (c : k ⟶ l) (w : W.obj (op (e, l)))
    (p : prism d t ⟶ J.obj k) (q : prism e t ⟶ J.obj l)
    (h : p ≫ J.map c = (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ q) :
    prismValue (W.map (show (d, k) ⟶ (e, l) from (a, c)).op w) p =
      (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ prismValue w q := by
  let f : (d, k) ⟶ (e, l) := (a, c)
  unfold prismValue
  rw [← generator_relation W f w, ← Category.assoc, ← Category.assoc, tFunctor_map]
  congr 1
  change lift (fst (std.obj d) (J.obj t)) p ≫ (std.map a ⊗ₘ J.map c) =
    (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ lift (fst (std.obj e) (J.obj t)) q
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
  · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd]
    exact h

/-- Restriction along the all-vertex sample gives the previously used row graph. -/
theorem sample_prismValue (w : W.obj (op (d, k))) (p : prism d t ⟶ J.obj k) :
    sample d t ≫ prismValue w p =
      (⟨k, W.map (show (code d t, k) ⟶ (d, k) from (horizontal d t, 𝟙 k)).op w,
        sample d t ≫ p⟩ : Graph W (code d t)).value := by
  let f : (code d t, k) ⟶ (d, k) := (horizontal d t, 𝟙 k)
  change sample d t ≫ (lift (fst (std.obj d) (J.obj t)) p ≫ _) =
    lift (𝟙 (std.obj (code d t))) (sample d t ≫ p) ≫ generator W _ (W.map f.op w)
  rw [← generator_relation W f w, ← Category.assoc, ← Category.assoc,
    tFunctor_map, J.map_id]
  congr 1

/-- Equality of full prism values for the same parameter determines the used coefficient. -/
theorem coefficient_eq_of_prismValue_eq (p : prism d t ⟶ J.obj k)
    (w v : W.obj (op (d, k))) (h : prismValue w p = prismValue v p) :
    W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
      (𝟙 d, inclusion (sample d t ≫ p))).op w =
    W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
      (𝟙 d, inclusion (sample d t ≫ p))).op v := by
  apply coefficient_on_full_support_eq p w v
  rw [← sample_prismValue w, ← sample_prismValue v, h]

/-- Pulling the coefficient back along a section recovers the exact descended prism value. -/
theorem prismValue_section (a : d ⟶ e) (b : e ⟶ d) (h : b ≫ a = 𝟙 e)
    (w : W.obj (op (d, k))) (p : prism d t ⟶ J.obj k) (q : prism e t ⟶ J.obj k)
    (r : prism e t ⟶ realization.obj W)
    (hp : p = (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ q)
    (hr : prismValue w p = (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ r) :
    prismValue (W.map (show (e, k) ⟶ (d, k) from (b, 𝟙 k)).op w) q = r := by
  have hs : (std.map b ⊗ₘ 𝟙 (J.obj t)) ≫ (std.map a ⊗ₘ 𝟙 (J.obj t)) =
      𝟙 (prism e t) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, ← std.map_comp, h, std.map_id]
    exact MonoidalCategory.id_tensorHom_id _ _
  have hq : q ≫ J.map (𝟙 k) = (std.map b ⊗ₘ 𝟙 (J.obj t)) ≫ p := by
    rw [hp, J.map_id, Category.comp_id, ← Category.assoc, hs, Category.id_comp]
  rw [prismValue_pullback b (𝟙 k) w q p hq, hr, ← Category.assoc, hs, Category.id_comp]

/-- When both the full parameter and the value descend, the old coefficient on
the full support is the pullback of the actual section-restricted coefficient. -/
theorem coefficient_eq_of_prismValue_splitEpi (a : d ⟶ e) (b : e ⟶ d)
    (h : b ≫ a = 𝟙 e) (w : W.obj (op (d, k))) (p : prism d t ⟶ J.obj k)
    (q : prism e t ⟶ J.obj k) (r : prism e t ⟶ realization.obj W)
    (hp : p = (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ q)
    (hr : prismValue w p = (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ r) :
    W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
      (𝟙 d, inclusion (sample d t ≫ p))).op w =
    W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (e, k) from
      (a, inclusion (sample d t ≫ p))).op
      (W.map (show (e, k) ⟶ (d, k) from (b, 𝟙 k)).op w) := by
  let v := W.map (show (e, k) ⟶ (d, k) from (b, 𝟙 k)).op w
  let f : (d, k) ⟶ (e, k) := (a, 𝟙 k)
  have hv := prismValue_section a b h w p q r hp hr
  have hc := prismValue_pullback a (𝟙 k) v p q (by rwa [J.map_id, Category.comp_id])
  rw [hv, ← hr] at hc
  have he := coefficient_eq_of_prismValue_eq p w (W.map f.op v) hc.symm
  rw [← FunctorToTypes.map_comp_apply, ← op_comp] at he
  have hf : (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
      (𝟙 d, inclusion (sample d t ≫ p))) ≫ f =
      (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (e, k) from
        (a, inclusion (sample d t ≫ p))) := by
    ext <;> simp [f]
  rw [hf] at he
  exact he

end
end DaggerModels.PartII.JTPrismRectangle
