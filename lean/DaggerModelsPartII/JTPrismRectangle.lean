import DaggerModelsPartII.JTRowGraphPointCoefficient
import Mathlib.Logic.Equiv.Fin.Basic

/-! One simplex of a bead prism sees all pairs of horizontal and time vertices. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTPrismRectangle

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective
open JTRowGraphParameterSupport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (d : SimplexCategory) := std.obj d

variable (d t : SimplexCategory)

/-- The ordinal which orders the rectangle by horizontal vertex first. -/
def code : SimplexCategory := ⦋((d.len + 1) * (t.len + 1)) - 1⦌

private theorem code_len : (code d t).len + 1 = (d.len + 1) * (t.len + 1) := by
  change (d.len + 1) * (t.len + 1) - 1 + 1 = _
  exact Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

/-- Read the horizontal and time vertices represented by an index of the rectangle. -/
def pairs : Fin ((code d t).len + 1) ≃ Fin (d.len + 1) × Fin (t.len + 1) :=
  finCongr (code_len d t) |>.trans finProdFinEquiv.symm

/-- The horizontal map repeats each vertex for each time vertex. -/
def horizontal : code d t ⟶ d :=
  SimplexCategory.Hom.mk ⟨fun j ↦ (pairs d t j).1, by
    intro i j h
    change i.val / (t.len + 1) ≤ j.val / (t.len + 1)
    exact Nat.div_le_div_right h⟩

/-- Use time vertex zero to give a section of the horizontal repetition. -/
def sectionMap : d ⟶ code d t :=
  SimplexCategory.Hom.mk ⟨fun i ↦ (pairs d t).symm (i, 0), by
    intro i j h
    change 0 + (t.len + 1) * i.val ≤ 0 + (t.len + 1) * j.val
    simpa only [Nat.zero_add] using Nat.mul_le_mul_left (t.len + 1) h⟩

theorem horizontal_split : sectionMap d t ≫ horizontal d t = 𝟙 d := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext i
  exact congrArg Prod.fst ((pairs d t).apply_symm_apply (i, 0))

private def timeNerve : (codiscreteNerve.obj (Fin (t.len + 1))).obj (op (code d t)) :=
  Codiscrete.functor fun j ↦ (pairs d t j).2

/-- The arbitrary groupoid time simplex lists all the time vertices over each
horizontal vertex, so time may restart at the next horizontal vertex. -/
def timeMap : Δ (code d t) ⟶ J.obj t :=
  SSet.yonedaEquiv.symm (timeNerve d t) ≫ (parameterCodiscreteIso.app t).inv

private theorem timeMap_label (i : Fin ((code d t).len + 1)) :
    label (timeMap d t) i = (pairs d t i).2 := by
  unfold label timeMap
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun x ↦ (x.obj i).as)
    (Equiv.apply_symm_apply SSet.yonedaEquiv (timeNerve d t))

/-- The prism simplex whose vertices cover the entire rectangle. -/
def sample : Δ (code d t) ⟶ Δ d ⊗ J.obj t :=
  lift (std.map (horizontal d t)) (timeMap d t)

private abbrev vertex (p : SimplexCategory) (i : Fin (p.len + 1)) :=
  SSet.yonedaEquiv (std.map (SimplexCategory.const ⦋0⦌ p i))

private theorem vertex_objEquiv {p : SimplexCategory} (u : (Δ p).obj (op ⦋0⦌)) :
    vertex p ((SSet.stdSimplex.objEquiv u).toOrderHom 0) = u := by
  apply SSet.stdSimplex.objEquiv.injective
  change SSet.stdSimplex.objEquiv.{0}
    (SSet.yonedaEquiv (std.map
      (SimplexCategory.const ⦋0⦌ p ((SSet.stdSimplex.objEquiv u).toOrderHom 0)))) = _
  rw [SSet.stdSimplex.yonedaEquiv_map, Equiv.apply_symm_apply]
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext l
  have hl : l = 0 := @Subsingleton.elim (Fin 1) inferInstance l 0
  subst l
  rfl

private theorem vertex_comp {p q : SimplexCategory} (u : p ⟶ q) (i : Fin (p.len + 1)) :
    (std.map u).app (op ⦋0⦌) (vertex p i) = vertex q (u.toOrderHom i) := by
  rw [← SSet.yonedaEquiv_comp, ← Functor.map_comp, SimplexCategory.const_comp]

private theorem label_vertex {m k : SimplexCategory} (s : Δ m ⟶ J.obj k)
    (i : Fin (m.len + 1)) :
    label s i = vertexLabels (parameterCodiscreteIso.app k).hom
      (s.app (op ⦋0⦌) (vertex m i)) := by
  let q := op (⦋0⦌ : SimplexCategory)
  let f := s ≫ (parameterCodiscreteIso.app k).hom
  let u := (⦋0⦌ : SimplexCategory).const m i
  have h := vertexLabels_natural f (op m) (SSet.yonedaEquiv (𝟙 (Δ m))) i
  have hz : (Δ m).map u.op (SSet.yonedaEquiv (𝟙 (Δ m))) = vertex m i := by
    rw [← SSet.yonedaEquiv_map_comp, Category.comp_id]
  rw [hz] at h
  rw [← SSet.yonedaEquiv_comp, Category.id_comp] at h
  exact h.symm

/-- Every zero simplex of the prism is hit by a vertex of the sample. -/
theorem sample_vertex_surjective :
    Function.Surjective ((sample d t).app (op ⦋0⦌)) := by
  rintro ⟨u, v⟩
  let i : Fin (d.len + 1) := (SSet.stdSimplex.objEquiv u).toOrderHom 0
  let j : Fin (t.len + 1) := vertexLabels (parameterCodiscreteIso.app t).hom v
  let h := (pairs d t).symm (i, j)
  refine ⟨vertex (code d t) h, ?_⟩
  apply Prod.ext
  · change (std.map (horizontal d t)).app (op ⦋0⦌) (vertex (code d t) h) = u
    rw [vertex_comp]
    have he : (horizontal d t).toOrderHom h = i :=
      congrArg Prod.fst ((pairs d t).apply_symm_apply (i, j))
    rw [he]
    exact vertex_objEquiv u
  · change (timeMap d t).app (op ⦋0⦌) (vertex (code d t) h) = v
    apply (CategoryTheory.mono_iff_injective ((parameterCodiscreteIso.app t).hom.app
      (op ⦋0⦌))).mp inferInstance
    apply nerve.ext_of_isThin
    funext l
    have hl : l = 0 := @Subsingleton.elim (Fin 1) inferInstance l 0
    subst l
    apply Codiscrete.ext
    change vertexLabels (parameterCodiscreteIso.app t).hom
      ((timeMap d t).app (op ⦋0⦌) (vertex (code d t) h)) = j
    rw [← label_vertex, timeMap_label]
    exact congrArg Prod.snd ((pairs d t).apply_symm_apply (i, j))

/-- The sampled row parameter uses exactly the labels appearing anywhere on the prism. -/
theorem used_sample_eq_range {k : SimplexCategory} (p : Δ d ⊗ J.obj t ⟶ J.obj k) :
    ((used (sample d t ≫ p) : Finset (Fin (k.len + 1))) : Set (Fin (k.len + 1))) =
      Set.range (fun x ↦ vertexLabels (parameterCodiscreteIso.app k).hom
        (p.app (op ⦋0⦌) x)) := by
  ext v
  change v ∈ used (sample d t ≫ p) ↔ _
  rw [used, Finset.mem_image]
  constructor
  · rintro ⟨i, _, hi⟩
    refine ⟨(sample d t).app (op ⦋0⦌) (vertex (code d t) i), ?_⟩
    exact (label_vertex (sample d t ≫ p) i).symm.trans hi
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := sample_vertex_surjective d t x
    let i := (SSet.stdSimplex.objEquiv y).toOrderHom 0
    have hyi : vertex (code d t) i = y := vertex_objEquiv y
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [label_vertex, hyi]
    change vertexLabels (parameterCodiscreteIso.app k).hom
      (p.app (op ⦋0⦌) ((sample d t).app (op ⦋0⦌) y)) = v
    rw [hy]
    exact hx

/-- If the sampled prism has a constant raw value, the entire coefficient
restricted to its used vertices is the degeneracy of that vertex. -/
theorem coefficient_of_sample {W : OrdinaryJTRealization.BiPresheaf} {k : SimplexCategory}
    (p : Δ d ⊗ J.obj t ⟶ J.obj k) (w : W.obj (op (d, k)))
    (v : W.obj (op (⦋0⦌, ⦋0⦌)))
    (h : (⟨k, W.map (show (code d t, k) ⟶ (d, k) from (horizontal d t, 𝟙 k)).op w,
      sample d t ≫ p⟩ : JTRowGraphRelations.Graph W (code d t)).value =
      std.map (SimplexCategory.isTerminalZero.from (code d t)) ≫
        (JTRowGraphPointCoefficient.pointGraph v).value) :
    W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (d, k) from
        (𝟙 d, inclusion (sample d t ≫ p))).op w =
      W.map (show (d, supportOrdinal (sample d t ≫ p)) ⟶ (⦋0⦌, ⦋0⦌) from
        (SimplexCategory.isTerminalZero.from d,
          SimplexCategory.isTerminalZero.from (supportOrdinal (sample d t ≫ p)))).op v := by
  let D := code d t
  let s := sample d t ≫ p
  let l := supportOrdinal s
  let a : (D, k) ⟶ (d, k) := (horizontal d t, 𝟙 k)
  let b : (D, l) ⟶ (D, k) := (𝟙 D, inclusion s)
  let c : (d, l) ⟶ (D, l) := (sectionMap d t, 𝟙 l)
  let e : (d, l) ⟶ (d, k) := (𝟙 d, inclusion s)
  let z (m : SimplexCategory) : (m, l) ⟶ (⦋0⦌, ⦋0⦌) :=
    (SimplexCategory.isTerminalZero.from m, SimplexCategory.isTerminalZero.from l)
  let G : JTRowGraphRelations.Graph W D := ⟨k, W.map a.op w, s⟩
  let H := JTRowGraphNormalForm.support G
  have hH : H.value = std.map (SimplexCategory.isTerminalZero.from D) ≫
      (JTRowGraphPointCoefficient.pointGraph v).value :=
    (JTRowGraphNormalForm.support_step G).value_eq.trans h
  have hv := JTRowGraphPointCoefficient.coefficient_of_point_value H v
    (source_vertex_surjective s) hH
  change W.map b.op (W.map a.op w) = W.map (z D).op v at hv
  have h₁ : c ≫ b ≫ a = e := by
    apply Prod.ext
    · change sectionMap d t ≫ 𝟙 D ≫ horizontal d t = 𝟙 d
      rw [Category.id_comp, horizontal_split]
    · change 𝟙 l ≫ inclusion s ≫ 𝟙 k = inclusion s
      rw [Category.comp_id, Category.id_comp]
  have h₂ : c ≫ z D = z d := by
    apply Prod.ext
    · exact SimplexCategory.isTerminalZero.hom_ext _ _
    · exact SimplexCategory.isTerminalZero.hom_ext _ _
  have hc := congrArg (W.map c.op) hv
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, ← Category.assoc] at hc
  change W.map (c ≫ b ≫ a).op w = W.map (c ≫ z D).op v at hc
  rw [h₁, h₂] at hc
  exact hc

end

end DaggerModels.PartII.JTPrismRectangle
