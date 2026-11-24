import DaggerModelsPartII.JTPrismRectangle
import DaggerModelsPartII.JTRowGraphCoefficientRigidity

/-! Recover coefficients on a whole timed bead from its actual sampled raw simplex. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTPrismRectangle

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphParameterSupport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Δ (d : SimplexCategory) := SSet.stdSimplex.{0}.obj d

/-- With the same entire timed parameter, equality of the two sampled raw
values gives equality of the bead coefficients on the full used support. -/
theorem coefficient_on_full_support_eq {W : BiPresheaf} {d t k : SimplexCategory}
    (p : Δ d ⊗ J.obj t ⟶ J.obj k) (w v : W.obj (op (d, k)))
    (h : (⟨k, W.map (show (code d t, k) ⟶ (d, k) from (horizontal d t, 𝟙 k)).op w,
      sample d t ≫ p⟩ : Graph W (code d t)).value =
      (⟨k, W.map (show (code d t, k) ⟶ (d, k) from (horizontal d t, 𝟙 k)).op v,
        sample d t ≫ p⟩ : Graph W (code d t)).value) :
    W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
      (𝟙 d, inclusion (sample d t ≫ p))).op w =
    W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
      (𝟙 d, inclusion (sample d t ≫ p))).op v := by
  let D := code d t
  let s := sample d t ≫ p
  let l := supportOrdinal s
  let a : (D, k) ⟶ (d, k) := (horizontal d t, 𝟙 k)
  let b : (D, l) ⟶ (D, k) := (𝟙 D, inclusion s)
  let c : (d, l) ⟶ (D, l) := (sectionMap d t, 𝟙 l)
  let e : (d, l) ⟶ (d, k) := (𝟙 d, inclusion s)
  have h' := JTRowGraphCoefficientRigidity.coefficient_on_support_eq
    (W.map a.op w) (W.map a.op v) s h
  change W.map b.op (W.map a.op w) = W.map b.op (W.map a.op v) at h'
  have he : c ≫ b ≫ a = e := by
    apply Prod.ext
    · change sectionMap d t ≫ 𝟙 D ≫ horizontal d t = 𝟙 d
      rw [Category.id_comp, horizontal_split]
    · change 𝟙 l ≫ inclusion s ≫ 𝟙 k = inclusion s
      rw [Category.comp_id, Category.id_comp]
  have hc := congrArg (W.map c.op) h'
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, ← Category.assoc] at hc
  change W.map (c ≫ b ≫ a).op w = W.map (c ≫ b ≫ a).op v at hc
  simpa only [he] using hc

end
end DaggerModels.PartII.JTPrismRectangle
