import DaggerModelsPartII.JTPrismHorizontalCoefficient
import DaggerModelsPartII.JTFullPrismSupport

/-! Actual coefficients on used vertices respect the horizontal, time and coefficient operators. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTPrismRectangle

open OrdinaryJTRealization JTRowGraphParameterSupport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (d : SimplexCategory) := std.obj d
private abbrev prism (d t : SimplexCategory) := Δ d ⊗ J.obj t

variable {W : BiPresheaf} {d e t t' k l : SimplexCategory}

/-- The full prism value commutes with arbitrary operators in the time coordinate. -/
theorem prismValue_time (m : t ⟶ t') (w : W.obj (op (d, k)))
    (p : prism d t' ⟶ J.obj k) :
    prismValue w ((𝟙 (Δ d) ⊗ₘ J.map m) ≫ p) =
      (𝟙 (Δ d) ⊗ₘ J.map m) ≫ prismValue w p := by
  unfold prismValue
  rw [← Category.assoc]
  congr 1

/-- The full prism realizes the simultaneous horizontal, time and coefficient operators. -/
theorem prismValue_mixed_pullback (a : d ⟶ e) (m : t ⟶ t') (b : k ⟶ l)
    (v : W.obj (op (e, l))) (p : prism d t ⟶ J.obj k) (q : prism e t' ⟶ J.obj l)
    (h : p ≫ J.map b = (std.map a ⊗ₘ J.map m) ≫ q) :
    prismValue (W.map (show (d, k) ⟶ (e, l) from (a, b)).op v) p =
      (std.map a ⊗ₘ J.map m) ≫ prismValue v q := by
  have hg : (std.map a ⊗ₘ 𝟙 (J.obj t)) ≫ (𝟙 (Δ e) ⊗ₘ J.map m) =
      std.map a ⊗ₘ J.map m := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [prismValue_pullback a b v p ((𝟙 (Δ e) ⊗ₘ J.map m) ≫ q) (by
    rw [← Category.assoc, hg]
    exact h), prismValue_time, ← Category.assoc, hg]

/-- The coefficient on the actual used support of a timed bead. -/
def usedCoefficient (w : W.obj (op (d, k))) (p : prism d t ⟶ J.obj k) :
    W.obj (op (d, supportOrdinal (sample d t ≫ p))) :=
  W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
    (𝟙 d, inclusion (sample d t ≫ p))).op w

/-- A compatible raw and parameter square is an exact operator between the
supported coefficients, with no choice of a tiny-time representative. -/
theorem usedCoefficient_mixed (a : d ⟶ e) (m : t ⟶ t') (b : k ⟶ l)
    (w : W.obj (op (d, k))) (v : W.obj (op (e, l)))
    (p : prism d t ⟶ J.obj k) (q : prism e t' ⟶ J.obj l)
    (hp : (std.map a ⊗ₘ J.map m) ≫ q = p ≫ J.map b)
    (hr : prismValue w p = (std.map a ⊗ₘ J.map m) ≫ prismValue v q) :
    usedCoefficient w p = W.map
      (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (e, supportOrdinal (sample e t' ≫ q))
        from (a, supportMap p q (std.map a ⊗ₘ J.map m) b hp)).op (usedCoefficient v q) := by
  let c := supportMap p q (std.map a ⊗ₘ J.map m) b hp
  let r : (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) :=
    (𝟙 d, inclusion (sample d t ≫ p))
  let s : (d, k) ⟶ (e, l) := (a, b)
  let r' : (e, supportOrdinal (sample e t' ≫ q)) ⟶ (e, l) :=
    (𝟙 e, inclusion (sample e t' ≫ q))
  let s' : (d, supportOrdinal (sample d t ≫ p)) ⟶ (e, supportOrdinal (sample e t' ≫ q)) :=
    (a, c)
  have hva := prismValue_mixed_pullback a m b v p q hp.symm
  have he := coefficient_eq_of_prismValue_eq p w (W.map s.op v) (hr.trans hva.symm)
  change W.map r.op w = W.map r.op (W.map s.op v) at he
  change W.map r.op w = W.map s'.op (W.map r'.op v)
  have hf : r ≫ s = s' ≫ r' := by
    apply Prod.ext
    · change 𝟙 d ≫ a = a ≫ 𝟙 e
      simp only [Category.id_comp, Category.comp_id]
    · exact (supportMap_inclusion p q _ b hp).symm
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← hf, op_comp, FunctorToTypes.map_comp_apply]
  exact he

end
end DaggerModels.PartII.JTPrismRectangle
