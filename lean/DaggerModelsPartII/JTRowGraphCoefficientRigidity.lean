import DaggerModelsPartII.JTRowGraphDegeneracyNormalization

/-! Coefficients of row graphs with one literal parameter are rigid on its used vertices. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTRowGraphCoefficientRigidity

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphCategory
open JTRowGraphNormalForm JTRowGraphParameterSupport
open JTRowGraphDegeneracyNormalization

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev row (W : BiPresheaf) (d : SimplexCategory) :=
  (JTRealizationDiagonal.ordinaryCurry.obj W).obj (op d)

variable {W : BiPresheaf} {d k : SimplexCategory}

/-- Equal raw row graphs with the same literal parameter have the same coefficient
on every parameter vertex that actually occurs. -/
theorem coefficient_on_support_eq (w v : W.obj (op (d, k)))
    (s : SSet.stdSimplex.{0}.obj d ⟶ J.obj k)
    (h : (⟨k, w, s⟩ : Graph W d).value = (⟨k, v, s⟩ : Graph W d).value) :
    (row W d).map (inclusion s).op w = (row W d).map (inclusion s).op v := by
  let G : Graph W d := ⟨k, w, s⟩
  let H : Graph W d := ⟨k, v, s⟩
  let q := G.value
  have hG : (support G).value = q := (support_step G).value_eq
  have hH : (support H).value = q := (support_step H).value_eq.trans h.symm
  let f : support G ⟶ canonical q :=
    toCanonicalOfSurjective (support G) (source_vertex_surjective s) ≫
      eqToHom (congrArg canonical hG)
  let g : support H ⟶ canonical q :=
    toCanonicalOfSurjective (support H) (source_vertex_surjective s) ≫
      eqToHom (congrArg canonical hH)
  have hop : f.operator = g.operator := by
    apply SimplexCategory.Hom.ext'
    apply OrderHom.ext
    funext x
    obtain ⟨i, hi⟩ := source_vertex_surjective s x
    have he := congrArg (fun t ↦ label t i) (f.parameter.trans g.parameter.symm)
    simp only [label_map] at he
    change f.operator.toOrderHom (label (source s) i) =
      g.operator.toOrderHom (label (source s) i) at he
    rw [hi] at he
    exact he
  change (support G).coefficient = (support H).coefficient
  calc
    (support G).coefficient = (row W d).map f.operator.op (canonical q).coefficient :=
      f.coefficient.symm
    _ = (row W d).map g.operator.op (canonical q).coefficient := by rw [hop]
    _ = (support H).coefficient := g.coefficient

/-- A horizontal split section recovers the coefficient on the original
parameter support when both the parameter and raw value descend along it. -/
theorem coefficient_on_support_eq_splitEpi {e : SimplexCategory}
    (G : Graph W d) (a : d ⟶ e) (b : e ⟶ d) (h : b ≫ a = 𝟙 e)
    (t : SSet.stdSimplex.{0}.obj e ⟶ J.obj G.degree)
    (q : SSet.stdSimplex.{0}.obj e ⟶ OrdinaryJTRealization.realization.obj W)
    (hp : G.parameter = SSet.stdSimplex.map a ≫ t)
    (hq : G.value = SSet.stdSimplex.map a ≫ q) :
    (row W d).map (inclusion G.parameter).op G.coefficient =
      (row W d).map (inclusion G.parameter).op
        (JTRowGraphResolution.restrictGraph a
          (JTRowGraphResolution.restrictGraph b G)).coefficient := by
  let K := JTRowGraphResolution.restrictGraph a
    (JTRowGraphResolution.restrictGraph b G)
  have hretract {Y : SSet.{0}} (u : SSet.stdSimplex.{0}.obj e ⟶ Y) :
      SSet.stdSimplex.map a ≫ SSet.stdSimplex.map b ≫
        (SSet.stdSimplex.map a ≫ u) = SSet.stdSimplex.map a ≫ u := by
    rw [← Category.assoc (SSet.stdSimplex.map b) (SSet.stdSimplex.map a) u,
      ← SSet.stdSimplex.map_comp, h]
    simp
  have hpK : K.parameter = G.parameter := by
    change SSet.stdSimplex.map a ≫ SSet.stdSimplex.map b ≫ G.parameter = G.parameter
    rw [hp, hretract]
  have hqK : K.value = G.value := by
    change (JTRowGraphResolution.restrictGraph a
      (JTRowGraphResolution.restrictGraph b G)).value = G.value
    rw [JTRowGraphResolution.restrictGraph_value,
      JTRowGraphResolution.restrictGraph_value, hq, hretract]
  have hK : K = ⟨G.degree, K.coefficient, G.parameter⟩ := by
    change (⟨G.degree, K.coefficient, K.parameter⟩ : Graph W d) = _
    rw [hpK]
  change (row W d).map (inclusion G.parameter).op G.coefficient =
    (row W d).map (inclusion G.parameter).op K.coefficient
  exact coefficient_on_support_eq G.coefficient K.coefficient G.parameter
    (by rw [← hK]; exact hqK.symm)

end

end DaggerModels.PartII.JTRowGraphCoefficientRigidity
