import DaggerModelsPartII.JTParameterLatchingMono

/-!
# Support of a simplex in the actual JT parameter

The existing natural isomorphism with the codiscrete nerve retains
the vertices of the actual free-groupoid parameter.  The source ordinal lists precisely the labels used by the simplex,
in their inherited order.  Postcomposition by an arbitrary simplex operator
induces a surjective operator between the two source ordinals.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTRowGraphParameterSupport

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective

noncomputable section

private abbrev Δ (d : SimplexCategory) := SSet.stdSimplex.{0}.obj d

variable {d k l : SimplexCategory}

/-- The actual parameter simplex, read through the existing codiscrete
comparison, is a list of vertex labels. -/
def label (s : Δ d ⟶ parameter.obj k) (i : Fin (d.len + 1)) :
    Fin (k.len + 1) :=
  ((SSet.yonedaEquiv
    (s ≫ (parameterCodiscreteIso.app k).hom)).obj i).as

/-- Naturality of the existing comparison, at every vertex of an arbitrary
simplex in the actual parameter. -/
theorem label_map (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l)
    (i : Fin (d.len + 1)) :
    label (s ≫ parameter.map j) i = j.toOrderHom (label s i) := by
  have hnat : parameter.map j ≫ (parameterCodiscreteIso.app l).hom =
      (parameterCodiscreteIso.app k).hom ≫ codiscreteNerve.map (vertices.map j) :=
    parameterCodiscreteIso.hom.naturality j
  have h :
      (s ≫ parameter.map j) ≫ (parameterCodiscreteIso.app l).hom =
        (s ≫ (parameterCodiscreteIso.app k).hom) ≫
          codiscreteNerve.map (vertices.map j) := by
    rw [Category.assoc, hnat, ← Category.assoc]
  have hi := congrArg
    (fun x ↦ ((SSet.yonedaEquiv x).obj i).as) h
  dsimp only at hi
  conv at hi =>
    rhs
    rw [SSet.yonedaEquiv_comp]
  change label (s ≫ parameter.map j) i =
    j.toOrderHom (label s i) at hi
  exact hi

/-- The nonempty set of labels occurring in the actual parameter simplex. -/
def used (s : Δ d ⟶ parameter.obj k) : Finset (Fin (k.len + 1)) :=
  Finset.univ.image (label s)

theorem label_mem_used (s : Δ d ⟶ parameter.obj k)
    (i : Fin (d.len + 1)) : label s i ∈ used s := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem used_nonempty (s : Δ d ⟶ parameter.obj k) : (used s).Nonempty := by
  exact ⟨label s 0, label_mem_used s 0⟩

/-- The ordinal with exactly the vertices used by `s`. -/
def supportOrdinal (s : Δ d ⟶ parameter.obj k) : SimplexCategory :=
  ⦋(used s).card - 1⦌

private theorem used_card (s : Δ d ⟶ parameter.obj k) :
    (used s).card = (supportOrdinal s).len + 1 := by
  dsimp [supportOrdinal]
  have hp : 0 < (used s).card := Finset.card_pos.mpr (used_nonempty s)
  omega

/-- Increasing enumeration of the used labels. -/
def supportOrderIso (s : Δ d ⟶ parameter.obj k) :
    Fin ((supportOrdinal s).len + 1) ≃o used s :=
  (used s).orderIsoOfFin (used_card s)

/-- The monotone injective inclusion of the support ordinal. -/
def inclusion (s : Δ d ⟶ parameter.obj k) : supportOrdinal s ⟶ k :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ (supportOrderIso s i).val, (supportOrderIso s).monotone⟩

theorem inclusion_injective (s : Δ d ⟶ parameter.obj k) :
    Function.Injective (inclusion s).toOrderHom := by
  intro a b h
  exact (supportOrderIso s).injective (Subtype.ext h)

theorem inclusion_mono (s : Δ d ⟶ parameter.obj k) :
    Mono (inclusion s) :=
  SimplexCategory.mono_iff_injective.mpr (inclusion_injective s)

/-- The coordinate of the `i`-th label in the support ordinal. -/
def sourceLabel (s : Δ d ⟶ parameter.obj k)
    (i : Fin (d.len + 1)) : Fin ((supportOrdinal s).len + 1) :=
  (supportOrderIso s).symm ⟨label s i, label_mem_used s i⟩

theorem sourceLabel_inclusion (s : Δ d ⟶ parameter.obj k)
    (i : Fin (d.len + 1)) :
    (inclusion s).toOrderHom (sourceLabel s i) = label s i := by
  change ((supportOrderIso s) ((supportOrderIso s).symm
    ⟨label s i, label_mem_used s i⟩)).val = label s i
  rw [OrderIso.apply_symm_apply]

theorem sourceLabel_surjective (s : Δ d ⟶ parameter.obj k) :
    Function.Surjective (sourceLabel s) := by
  intro v
  have hv : ((supportOrderIso s) v).val ∈ used s :=
    ((supportOrderIso s) v).property
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
  refine ⟨i, ?_⟩
  unfold sourceLabel
  have he : (supportOrderIso s) v =
      (⟨label s i, label_mem_used s i⟩ : used s) := by
    apply Subtype.ext
    exact hi.symm
  rw [← he, OrderIso.symm_apply_apply]

/-- The codiscrete simplex with the support coordinates as labels. -/
private def sourceCodiscrete (s : Δ d ⟶ parameter.obj k) :
    (codiscreteNerve.obj
      (Fin ((supportOrdinal s).len + 1))).obj (op d) :=
  Codiscrete.functor (sourceLabel s)

/-- The support simplex in the actual free-groupoid parameter. -/
def source (s : Δ d ⟶ parameter.obj k) :
    Δ d ⟶ parameter.obj (supportOrdinal s) :=
  SSet.yonedaEquiv.symm (sourceCodiscrete s) ≫
    (parameterCodiscreteIso.app (supportOrdinal s)).inv

theorem source_label (s : Δ d ⟶ parameter.obj k)
    (i : Fin (d.len + 1)) :
    label (source s) i = sourceLabel s i := by
  unfold label source
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun x ↦ (x.obj i).as)
    (Equiv.apply_symm_apply SSet.yonedaEquiv (sourceCodiscrete s))

/-- The source simplex has all support vertices, so it has no unused
parameter vertices. -/
theorem source_vertex_surjective (s : Δ d ⟶ parameter.obj k) :
    Function.Surjective (label (source s)) := by
  simpa only [source_label] using sourceLabel_surjective s

private theorem label_ext {s t : Δ d ⟶ parameter.obj k}
    (h : ∀ i, label s i = label t i) : s = t := by
  apply (cancel_mono (parameterCodiscreteIso.app k).hom).mp
  apply SSet.yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  exact Codiscrete.ext (h i)

/-- The full actual parameter simplex factors through its used vertices. -/
theorem source_factor (s : Δ d ⟶ parameter.obj k) :
    source s ≫ parameter.map (inclusion s) = s := by
  apply label_ext
  intro i
  rw [label_map, source_label, sourceLabel_inclusion]

/-- Every used label remains used after applying an ordinal operator. -/
private theorem mapped_label_mem (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l)
    (v : Fin ((supportOrdinal s).len + 1)) :
    j.toOrderHom ((inclusion s).toOrderHom v) ∈
      used (s ≫ parameter.map j) := by
  obtain ⟨i, hi⟩ := sourceLabel_surjective s v
  rw [← hi, sourceLabel_inclusion, ← label_map]
  exact label_mem_used (s ≫ parameter.map j) i

/-- The induced monotone operator between the support ordinals. -/
def supportMap (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l) :
    supportOrdinal s ⟶ supportOrdinal (s ≫ parameter.map j) :=
  SimplexCategory.Hom.mk
    { toFun := fun v ↦
        (supportOrderIso (s ≫ parameter.map j)).symm
          ⟨j.toOrderHom ((inclusion s).toOrderHom v),
            mapped_label_mem s j v⟩
      monotone' := by
        intro a b hab
        apply (supportOrderIso (s ≫ parameter.map j)).symm.monotone
        exact j.toOrderHom.monotone
          ((inclusion s).toOrderHom.monotone hab) }

/-- The support operator is forced by the commuting square of ordinal maps. -/
theorem supportMap_inclusion (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l) :
    supportMap s j ≫ inclusion (s ≫ parameter.map j) =
      inclusion s ≫ j := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext v
  change (inclusion (s ≫ parameter.map j)).toOrderHom ((supportMap s j).toOrderHom v) =
    j.toOrderHom ((inclusion s).toOrderHom v)
  let w : used (s ≫ parameter.map j) :=
    ⟨j.toOrderHom ((inclusion s).toOrderHom v), mapped_label_mem s j v⟩
  exact congrArg Subtype.val ((supportOrderIso (s ≫ parameter.map j)).apply_symm_apply w)

/-- The induced operator hits every vertex of the new support. -/
theorem supportMap_surjective (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l) :
    Function.Surjective (supportMap s j).toOrderHom := by
  intro v
  obtain ⟨i, hi⟩ := sourceLabel_surjective
    (s ≫ parameter.map j) v
  refine ⟨sourceLabel s i, ?_⟩
  apply (inclusion_injective (s ≫ parameter.map j))
  have hc := SimplexCategory.congr_toOrderHom_apply
    (supportMap_inclusion s j) (sourceLabel s i)
  calc
    (inclusion (s ≫ parameter.map j)).toOrderHom
        ((supportMap s j).toOrderHom (sourceLabel s i)) =
      j.toOrderHom ((inclusion s).toOrderHom (sourceLabel s i)) := by
        simpa only [SimplexCategory.comp_toOrderHom] using hc
    _ = label (s ≫ parameter.map j) i := by
      rw [sourceLabel_inclusion, label_map]
    _ = (inclusion (s ≫ parameter.map j)).toOrderHom v := by
      rw [← hi, sourceLabel_inclusion]

theorem supportMap_epi (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l) :
    Epi (supportMap s j) :=
  SimplexCategory.epi_iff_surjective.mpr (supportMap_surjective s j)

/-- Any ordinal map commuting with the support inclusions is the induced
support map, including when `j` is neither injective nor surjective. -/
theorem supportMap_unique (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l)
    (u : supportOrdinal s ⟶ supportOrdinal (s ≫ parameter.map j))
    (hu : u ≫ inclusion (s ≫ parameter.map j) = inclusion s ≫ j) :
    u = supportMap s j := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext v
  apply inclusion_injective (s ≫ parameter.map j)
  have h₁ := SimplexCategory.congr_toOrderHom_apply hu v
  have h₂ := SimplexCategory.congr_toOrderHom_apply
    (supportMap_inclusion s j) v
  simpa only [SimplexCategory.comp_toOrderHom] using h₁.trans h₂.symm

/-- The actual parameter maps commute with the canonical source simplex. -/
theorem source_map (s : Δ d ⟶ parameter.obj k) (j : k ⟶ l) :
    source s ≫ parameter.map (supportMap s j) =
      source (s ≫ parameter.map j) := by
  apply label_ext
  intro i
  rw [label_map, source_label, source_label]
  apply inclusion_injective (s ≫ parameter.map j)
  have hc := SimplexCategory.congr_toOrderHom_apply
    (supportMap_inclusion s j) (sourceLabel s i)
  calc
    (inclusion (s ≫ parameter.map j)).toOrderHom
        ((supportMap s j).toOrderHom (sourceLabel s i)) =
        j.toOrderHom ((inclusion s).toOrderHom (sourceLabel s i)) := by
      simpa only [SimplexCategory.comp_toOrderHom] using hc
    _ = _ := by rw [sourceLabel_inclusion, sourceLabel_inclusion, label_map]

end

end DaggerModels.PartII.JTRowGraphParameterSupport
