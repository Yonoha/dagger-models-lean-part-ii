import DaggerModelsPartII.JTFiniteCoefficientBridgeOrder
import DaggerModelsPartII.JTCommonCoefficientBaseChange

/-! Reindex the coefficient bridge in the source, time, and ordered copy indices. -/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeMixedOrder

open JTFiniteCoefficientBridgeOrder
open JTHigherInterleavedParameter (common)

noncomputable section

variable {m m' : ℕ} {k l n n' b : SimplexCategory}
variable {B : Fin (m + 1) → SimplexCategory} {C : Fin (m' + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ B e) (d : ∀ e, l ⟶ C e)
variable (f : k ⟶ l) (j : n ⟶ n') (a : ⦋m⦌ ⟶ ⦋m'⦌)

private abbrev applyPair (x : Fin (k.len + 1) × Fin (n.len + 1)) :=
  (f.toOrderHom x.1, j.toOrderHom x.2)

/-- Every retained copy preserves its intrinsic coefficient-time order. -/
def RespectsRanks : Prop :=
  ∀ (e : Fin (m + 1)) (x y : Fin (k.len + 1) × Fin (n.len + 1)),
    JTCommonCoefficientParameter.vertexEquiv (c e) n x ≤
      JTCommonCoefficientParameter.vertexEquiv (c e) n y →
    JTCommonCoefficientParameter.vertexEquiv (d (a.toOrderHom e)) n' (applyPair f j x) ≤
      JTCommonCoefficientParameter.vertexEquiv (d (a.toOrderHom e)) n' (applyPair f j y)

/-- The actual ordinal action on each copy proves the required rank condition. -/
theorem ranks_of_operators
    (v : Fin (m + 1) → (common k n ⟶ common l n'))
    (hv : ∀ e x, (v e).toOrderHom (JTCommonCoefficientParameter.vertexEquiv (c e) n x) =
      JTCommonCoefficientParameter.vertexEquiv (d (a.toOrderHom e)) n' (applyPair f j x)) :
    RespectsRanks c d f j a := by
  intro e x y h
  rw [← hv e x, ← hv e y]
  exact (v e).toOrderHom.monotone h

/-- Copywise base change is allowed whenever it retains the source rank. -/
theorem ranks_of_baseChange (hj : Function.Injective j.toOrderHom)
    (v : ∀ e, B e ⟶ C (a.toOrderHom e))
    (hv : ∀ e, f ≫ d (a.toOrderHom e) = c e ≫ v e)
    (h : ∀ e x y, (v e).toOrderHom ((c e).toOrderHom x) =
      (v e).toOrderHom ((c e).toOrderHom y) → (c e).toOrderHom x = (c e).toOrderHom y) :
    RespectsRanks c d f j a := by
  refine ranks_of_operators c d f j a
    (fun e ↦ JTCommonCoefficientParameter.map f (hv e) j hj) ?_
  intro e x
  rw [← JTCommonCoefficientParameter.vertexEquiv_comp_eq (c e) (v e) (h e) n]
  exact JTCommonCoefficientParameter.map_vertexEquiv f (hv e) j hj x

variable {u : k ⟶ b} {u' : l ⟶ b}
variable (hu : f ≫ u' = u) (ha : Function.Injective a.toOrderHom)
variable (hr : RespectsRanks c d f j a)

private theorem base_eq (hu : f ≫ u' = u) (v : Fin (k.len + 1)) :
    u'.toOrderHom (f.toOrderHom v) = u.toOrderHom v :=
  SimplexCategory.congr_toOrderHom_apply hu v

/-- Reindex the exact bridge, with the final coefficient preserved and all
horizontal coefficient and time coordinates carried to their images. -/
def map : bridge k n m ⟶ bridge l n' m' :=
  SimplexCategory.Hom.mk ⟨fun z ↦
    let x := (vertexEquiv c u n).symm z
    vertexEquiv d u' n' (applyPair f j x.1, a.toOrderHom x.2), by
    intro z z' hz
    obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective z
    obtain ⟨y, rfl⟩ := (vertexEquiv c u n).surjective z'
    simp only [Equiv.symm_apply_apply]
    have h := (vertex_le_iff c u n x y).1 hz
    apply (vertex_le_iff d u' n' _ _).2
    change u'.toOrderHom (f.toOrderHom x.1.1) ≤ u'.toOrderHom (f.toOrderHom y.1.1) ∧ _
    refine ⟨?_, ?_⟩
    · rw [base_eq f hu, base_eq f hu]
      exact h.1
    · intro he
      change u'.toOrderHom (f.toOrderHom x.1.1) = u'.toOrderHom (f.toOrderHom y.1.1) at he
      rw [base_eq f hu, base_eq f hu] at he
      refine ⟨a.toOrderHom.monotone (h.2 he).1, fun hcopy ↦ ?_⟩
      have heq := ha hcopy
      have hold := (h.2 he).2 heq
      rcases x with ⟨x, e⟩
      rcases y with ⟨y, e'⟩
      change e = e' at heq
      subst e'
      exact hr e x y hold⟩

@[simp]
theorem map_vertex (x : Vertex k n m) :
    (map c d f j a hu ha hr).toOrderHom (vertexEquiv c u n x) =
      vertexEquiv d u' n' (applyPair f j x.1, a.toOrderHom x.2) := by
  change vertexEquiv d u' n'
    (applyPair f j ((vertexEquiv c u n).symm (vertexEquiv c u n x)).1,
      a.toOrderHom ((vertexEquiv c u n).symm (vertexEquiv c u n x)).2) = _
  rw [Equiv.symm_apply_apply]

theorem map_base :
    map c d f j a hu ha hr ≫ base d u' n' = base c u n := by
  ext z : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective z
  change (base d u' n').toOrderHom
      ((map c d f j a hu ha hr).toOrderHom (vertexEquiv c u n x)) = _
  rw [map_vertex, base_vertexEquiv, base_vertexEquiv]
  exact base_eq f hu x.1.1

/-- The entire inclusion of each retained copy commutes with its own map. -/
theorem side_map (h : ∀ e, B e ⟶ b) (h' : ∀ e, C e ⟶ b)
    (hc : ∀ e, c e ≫ h e = u) (hd : ∀ e, d e ≫ h' e = u')
    (e : Fin (m + 1)) (v : common k n ⟶ common l n')
    (hv : ∀ x, v.toOrderHom (JTCommonCoefficientParameter.vertexEquiv (c e) n x) =
      JTCommonCoefficientParameter.vertexEquiv (d (a.toOrderHom e)) n' (applyPair f j x)) :
    side c u h hc n e ≫ map c d f j a hu ha hr =
      v ≫ side d u' h' hd n' (a.toOrderHom e) := by
  ext z : 3
  obtain ⟨x, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv (c e) n).surjective z
  change (map c d f j a hu ha hr).toOrderHom
      ((side c u h hc n e).toOrderHom (JTCommonCoefficientParameter.vertexEquiv (c e) n x)) =
    (side d u' h' hd n' (a.toOrderHom e)).toOrderHom
      (v.toOrderHom (JTCommonCoefficientParameter.vertexEquiv (c e) n x))
  rw [side_vertexEquiv, map_vertex, hv, side_vertexEquiv]

theorem ranks_id : RespectsRanks c c (𝟙 k) (𝟙 n) (𝟙 ⦋m⦌) :=
  fun _ _ _ h ↦ h

theorem map_id :
    map c c (𝟙 k) (𝟙 n) (𝟙 ⦋m⦌) (Category.id_comp u) (fun _ _ e ↦ e) (ranks_id c) =
      𝟙 (bridge k n m) := by
  ext z : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective z
  rw [map_vertex]
  rfl

include hr in
theorem ranks_comp {r : ℕ} {p n'' : SimplexCategory}
    {D : Fin (r + 1) → SimplexCategory} (e : ∀ t, p ⟶ D t)
    (f' : l ⟶ p) (j' : n' ⟶ n'') (a' : ⦋m'⦌ ⟶ ⦋r⦌)
    (hr' : RespectsRanks d e f' j' a') :
    RespectsRanks c e (f ≫ f') (j ≫ j') (a ≫ a') :=
  fun t x y h ↦ hr' (a.toOrderHom t) (applyPair f j x) (applyPair f j y) (hr t x y h)

theorem map_comp {r : ℕ} {p n'' : SimplexCategory}
    {D : Fin (r + 1) → SimplexCategory} (e : ∀ t, p ⟶ D t)
    {u'' : p ⟶ b} (f' : l ⟶ p) (j' : n' ⟶ n'') (a' : ⦋m'⦌ ⟶ ⦋r⦌)
    (hu' : f' ≫ u'' = u') (ha' : Function.Injective a'.toOrderHom)
    (hr' : RespectsRanks d e f' j' a') :
    map c e (f ≫ f') (j ≫ j') (a ≫ a') (by rw [Category.assoc, hu', hu])
      (ha'.comp ha) (ranks_comp c d f j a hr e f' j' a' hr') =
    map c d f j a hu ha hr ≫ map d e f' j' a' hu' ha' hr' := by
  ext z : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective z
  change (map c e (f ≫ f') (j ≫ j') (a ≫ a') _ (ha'.comp ha) (ranks_comp c d f j a hr e f' j' a' hr')).toOrderHom
      (vertexEquiv c u n x) =
    (map d e f' j' a' hu' ha' hr').toOrderHom
      ((map c d f j a hu ha hr).toOrderHom (vertexEquiv c u n x))
  simp only [map_vertex]
  rfl

end
end DaggerModels.PartII.JTFiniteCoefficientBridgeMixedOrder
