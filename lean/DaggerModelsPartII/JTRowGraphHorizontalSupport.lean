import DaggerModelsPartII.JTRowGraphResolution

/-!
# Used-vertex support for the two original row-graph operators

A horizontal restriction may discard parameter vertices. Keeping its actual
support gives maps over the common original coefficient, also when the horizontal
or coefficient operator has degeneracies.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.JTRowGraphHorizontalSupport

open GroupoidSimplex JTRowGraphParameterSupport

noncomputable section

private abbrev Δ (d : SimplexCategory) := SSet.stdSimplex.{0}.obj d
private abbrev J := parameter

variable {d e f k l m : SimplexCategory}

theorem label_restriction (a : d ⟶ e) (t : Δ e ⟶ J.obj l) (i : Fin (d.len + 1)) :
    label (SSet.stdSimplex.map a ≫ t) i = label t (a.toOrderHom i) := by
  unfold label
  rw [Category.assoc, SSet.yonedaEquiv_map_comp]
  rfl

private theorem mapped_label_mem {s : Δ d ⟶ J.obj k} {t : Δ e ⟶ J.obj l}
    (a : d ⟶ e) (b : k ⟶ l) (h : s ≫ J.map b = SSet.stdSimplex.map a ≫ t)
    (v : Fin ((supportOrdinal s).len + 1)) :
    b.toOrderHom ((inclusion s).toOrderHom v) ∈ used t := by
  obtain ⟨i, rfl⟩ := sourceLabel_surjective s v
  rw [sourceLabel_inclusion, ← label_map, h, label_restriction]
  exact label_mem_used t (a.toOrderHom i)

/-- The actual operator between used vertices of a compatible pair of row graphs. -/
def operator {s : Δ d ⟶ J.obj k} {t : Δ e ⟶ J.obj l}
    (a : d ⟶ e) (b : k ⟶ l) (h : s ≫ J.map b = SSet.stdSimplex.map a ≫ t) :
    supportOrdinal s ⟶ supportOrdinal t :=
  SimplexCategory.Hom.mk
    ⟨fun v ↦ (supportOrderIso t).symm
      ⟨b.toOrderHom ((inclusion s).toOrderHom v), mapped_label_mem a b h v⟩,
     fun _ _ hv ↦ (supportOrderIso t).symm.monotone
       (b.toOrderHom.monotone ((inclusion s).toOrderHom.monotone hv))⟩

@[reassoc]
theorem operator_inclusion {s : Δ d ⟶ J.obj k} {t : Δ e ⟶ J.obj l}
    (a : d ⟶ e) (b : k ⟶ l) (h : s ≫ J.map b = SSet.stdSimplex.map a ≫ t) :
    operator a b h ≫ inclusion t = inclusion s ≫ b := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext v
  let w : used t :=
    ⟨b.toOrderHom ((inclusion s).toOrderHom v), mapped_label_mem a b h v⟩
  exact congrArg Subtype.val ((supportOrderIso t).apply_symm_apply w)

/-- The original parameter equations survive on the entire supported graph. -/
theorem operator_parameter {s : Δ d ⟶ J.obj k} {t : Δ e ⟶ J.obj l}
    (a : d ⟶ e) (b : k ⟶ l) (h : s ≫ J.map b = SSet.stdSimplex.map a ≫ t) :
    source s ≫ J.map (operator a b h) = SSet.stdSimplex.map a ≫ source t := by
  apply (cancel_mono (parameterCodiscreteIso.app (supportOrdinal t)).hom).mp
  apply SSet.yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  change label (source s ≫ J.map (operator a b h)) i =
    label (SSet.stdSimplex.map a ≫ source t) i
  rw [label_map, label_restriction, source_label, source_label]
  apply inclusion_injective t
  have hi := SimplexCategory.congr_toOrderHom_apply (operator_inclusion a b h) (sourceLabel s i)
  change (inclusion t).toOrderHom ((operator a b h).toOrderHom (sourceLabel s i)) =
    b.toOrderHom ((inclusion s).toOrderHom (sourceLabel s i)) at hi
  rw [hi, sourceLabel_inclusion, sourceLabel_inclusion, ← label_map, h, label_restriction]

/-- Composing mixed operators preserves the induced support operator. -/
theorem operator_comp {s : Δ d ⟶ J.obj k} {t : Δ e ⟶ J.obj l} {u : Δ f ⟶ J.obj m}
    (a : d ⟶ e) (a' : e ⟶ f) (b : k ⟶ l) (b' : l ⟶ m)
    (h : s ≫ J.map b = SSet.stdSimplex.map a ≫ t)
    (h' : t ≫ J.map b' = SSet.stdSimplex.map a' ≫ u)
    (h'' : s ≫ J.map (b ≫ b') = SSet.stdSimplex.map (a ≫ a') ≫ u) :
    operator a b h ≫ operator a' b' h' = operator (a ≫ a') (b ≫ b') h'' := by
  letI := inclusion_mono u
  apply (cancel_mono (inclusion u)).mp
  rw [Category.assoc, operator_inclusion, operator_inclusion_assoc, operator_inclusion]

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphCategory
open JTRowGraphResolution JTRowGraphNormalForm

variable {W : BiPresheaf}

/-- A mixed row-graph arrow restricts to the two actual used supports. -/
def supportedArrow {G : Graph W d} {H : Graph W e}
    (a : d ⟶ e) (g : G ⟶ restrictGraph a H) :
    support G ⟶ restrictGraph a (support H) := by
  let b := g.operator
  have hp : G.parameter ≫ J.map b = SSet.stdSimplex.map a ≫ H.parameter := g.parameter
  let c := operator a b hp
  refine ⟨c, ?_, operator_parameter a b hp⟩
  let i := inclusion G.parameter
  let j := inclusion H.parameter
  let x : (d, G.degree) ⟶ (e, H.degree) := (a, b)
  let y : (d, supportOrdinal G.parameter) ⟶ (e, H.degree) := (a, i ≫ b)
  have hg : W.map x.op H.coefficient = G.coefficient := by
    have hx : ((𝟙 d, b) : (d, G.degree) ⟶ (d, H.degree)) ≫ (a, 𝟙 H.degree) = x := by
      ext <;> simp [x]
    have h := g.coefficient
    change W.map (Quiver.Hom.op ((𝟙 d, b) : (d, G.degree) ⟶ (d, H.degree)))
      (W.map (Quiver.Hom.op ((a, 𝟙 H.degree) : (d, H.degree) ⟶ (e, H.degree))) H.coefficient) =
      G.coefficient at h
    rw [← hx, op_comp, Functor.map_comp, types_comp_apply]
    exact h
  let c₁ : (d, supportOrdinal G.parameter) ⟶ (d, supportOrdinal H.parameter) := (𝟙 d, c)
  let c₂ : (d, supportOrdinal H.parameter) ⟶ (e, supportOrdinal H.parameter) :=
    (a, 𝟙 (supportOrdinal H.parameter))
  let c₃ : (e, supportOrdinal H.parameter) ⟶ (e, H.degree) := (𝟙 e, j)
  let c₄ : (d, supportOrdinal G.parameter) ⟶ (d, G.degree) := (𝟙 d, i)
  have hleft : c₁ ≫ c₂ ≫ c₃ = y := by
    apply Prod.ext
    · change 𝟙 d ≫ a ≫ 𝟙 e = a
      simp
    · change c ≫ 𝟙 _ ≫ j = i ≫ b
      rw [Category.id_comp]
      exact operator_inclusion a b hp
  have hright : c₄ ≫ x = y := by
    apply Prod.ext
    · exact Category.id_comp a
    · rfl
  have h := congrArg (fun v : (d, supportOrdinal G.parameter) ⟶ (e, H.degree) ↦
    W.map v.op H.coefficient) (hleft.trans hright.symm)
  simpa only [op_comp, Functor.map_comp, types_comp_apply, hg] using h

/-- Support of a restricted row graph maps naturally to restriction of its support. -/
def restrictionComparison (W : BiPresheaf) (a : d ⟶ e) :
    restrict W a ⋙ supportFunctor W d ⟶ supportFunctor W e ⋙ restrict W a where
  app G := supportedArrow a (𝟙 (restrictGraph a G))
  naturality G H g := by
    let X := support (restrictGraph a G)
    let Y := restrictGraph a (support H)
    have h : Function.Surjective (label X.parameter) :=
      source_vertex_surjective (restrictGraph a G).parameter
    exact @hom_ext_of_label_surjective W d X Y h _ _

end

end DaggerModels.PartII.JTRowGraphHorizontalSupport
