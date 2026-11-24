import DaggerModelsPartII.JTHigherInterleavedOperators
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort

/-!
# Ordered prism parameters over a common coefficient

A vertex is a pair of a source vertex and a time vertex. Order these
pairs by their image in the common coefficient, then by time, then by
the source vertex.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)

noncomputable section

variable {k l b n m : SimplexCategory}

/-- Carry the chosen ordering data in the vertex type. -/
def Vertex (_c : k ⟶ b) (n : SimplexCategory) :=
  Fin (k.len + 1) × Fin (n.len + 1)

private def coordinates (c : k ⟶ b) (n : SimplexCategory) :
    Vertex c n ≃ Fin (k.len + 1) × Fin (n.len + 1) :=
  Equiv.refl _

private def key (c : k ⟶ b) (n : SimplexCategory) (x : Vertex c n) :
    Fin (b.len + 1) ×ₗ (Fin (n.len + 1) ×ₗ Fin (k.len + 1)) :=
  let p := coordinates c n x
  toLex (c.toOrderHom p.1, toLex (p.2, p.1))

private theorem key_injective (c : k ⟶ b) (n : SimplexCategory) :
    Function.Injective (key c n) := by
  intro x y h
  apply (coordinates c n).injective
  have h' := congrArg (fun z ↦ ofLex (ofLex z).2) h
  exact Prod.ext (congrArg Prod.snd h') (congrArg Prod.fst h')

instance (c : k ⟶ b) (n : SimplexCategory) : LinearOrder (Vertex c n) :=
  LinearOrder.lift' (key c n) (key_injective c n)

instance (c : k ⟶ b) (n : SimplexCategory) : Fintype (Vertex c n) :=
  Fintype.ofEquiv _ (coordinates c n).symm

private theorem card (c : k ⟶ b) (n : SimplexCategory) :
    Fintype.card (Vertex c n) = (common k n).len + 1 := by
  rw [Fintype.card_congr (coordinates c n), Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  change (k.len + 1) * (n.len + 1) = k.len * (n.len + 1) + n.len + 1
  rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

private def rank (c : k ⟶ b) (n : SimplexCategory) :
    Vertex c n ≃o Fin ((common k n).len + 1) :=
  (Fintype.orderIsoFinOfCardEq _ (card c n)).symm

/-- The vertices of the larger standard simplex, in the indicated order. -/
def vertexEquiv (c : k ⟶ b) (n : SimplexCategory) :
    Fin (k.len + 1) × Fin (n.len + 1) ≃ Fin ((common k n).len + 1) :=
  (coordinates c n).symm.trans (rank c n).toEquiv

theorem vertex_le_iff (c : k ⟶ b) (n : SimplexCategory)
    (x y : Fin (k.len + 1) × Fin (n.len + 1)) :
    vertexEquiv c n x ≤ vertexEquiv c n y ↔
      c.toOrderHom x.1 ≤ c.toOrderHom y.1 ∧
        (c.toOrderHom x.1 = c.toOrderHom y.1 →
          x.2 ≤ y.2 ∧ (x.2 = y.2 → x.1 ≤ y.1)) := by
  change rank c n ((coordinates c n).symm x) ≤ rank c n ((coordinates c n).symm y) ↔ _
  rw [OrderIso.le_iff_le]
  change toLex (c.toOrderHom x.1, toLex (x.2, x.1)) ≤
    toLex (c.toOrderHom y.1, toLex (y.2, y.1)) ↔ _
  simp only [Prod.Lex.toLex_le_toLex']

/-- The ordinary product order embeds in the ordered parameter. -/
def prismOrder (c : k ⟶ b) (n : SimplexCategory) :
    Fin (k.len + 1) × Fin (n.len + 1) →o Fin ((common k n).len + 1) :=
  ⟨vertexEquiv c n, fun x y h ↦ (vertex_le_iff c n x y).2
    ⟨c.toOrderHom.monotone h.1, fun _ ↦ ⟨h.2, fun _ ↦ h.1⟩⟩⟩

/-- Projection to the common coefficient, including when it identifies
source vertices. -/
def base (c : k ⟶ b) (n : SimplexCategory) : common k n ⟶ b :=
  SimplexCategory.Hom.mk ⟨fun x ↦ c.toOrderHom ((vertexEquiv c n).symm x).1, by
    intro x y h
    obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective x
    obtain ⟨y, rfl⟩ := (vertexEquiv c n).surjective y
    simpa only [Equiv.symm_apply_apply] using ((vertex_le_iff c n x y).1 h).1⟩

@[simp] theorem base_vertexEquiv (c : k ⟶ b) (n : SimplexCategory)
    (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (base c n).toOrderHom (vertexEquiv c n x) = c.toOrderHom x.1 := by
  change c.toOrderHom ((vertexEquiv c n).symm (vertexEquiv c n x)).1 = _
  rw [Equiv.symm_apply_apply]

/-- The source coefficient in one time slice. -/
def slice (c : k ⟶ b) (n : SimplexCategory) (t : Fin (n.len + 1)) : k ⟶ common k n :=
  SimplexCategory.Hom.mk ⟨fun a ↦ vertexEquiv c n (a, t),
    fun _ _ h ↦ (prismOrder c n).monotone ⟨h, le_rfl⟩⟩

/-- The full time simplex at a chosen source vertex. -/
def vertical (c : k ⟶ b) (n : SimplexCategory) (a : Fin (k.len + 1)) : n ⟶ common k n :=
  SimplexCategory.Hom.mk ⟨fun t ↦ vertexEquiv c n (a, t),
    fun _ _ h ↦ (prismOrder c n).monotone ⟨le_rfl, h⟩⟩

theorem slice_base (c : k ⟶ b) (n : SimplexCategory) (t : Fin (n.len + 1)) :
    slice c n t ≫ base c n = c := by
  ext a : 3
  exact base_vertexEquiv c n (a, t)

private theorem coeff_eq {c : k ⟶ b} {d : l ⟶ b} {f : k ⟶ l}
    (hf : f ≫ d = c) (a : Fin (k.len + 1)) :
    d.toOrderHom (f.toOrderHom a) = c.toOrderHom a :=
  congrArg (fun h : k ⟶ b ↦ h.toOrderHom a) hf

/-- The coefficient operator can be arbitrary over the same common
base. The time operator is an order embedding. -/
def map {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) :
    common k n ⟶ common l m :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    let x := (vertexEquiv c n).symm v
    vertexEquiv d m (f.toOrderHom x.1, j.toOrderHom x.2), by
    intro v w h
    obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective v
    obtain ⟨y, rfl⟩ := (vertexEquiv c n).surjective w
    simp only [Equiv.symm_apply_apply]
    have h' := (vertex_le_iff c n x y).1 h
    apply (vertex_le_iff d m _ _).2
    rw [coeff_eq hf, coeff_eq hf]
    exact ⟨h'.1, fun he ↦ ⟨j.toOrderHom.monotone (h'.2 he).1,
      fun ht ↦ f.toOrderHom.monotone ((h'.2 he).2 (hj ht))⟩⟩⟩

@[simp] theorem map_vertexEquiv {c : k ⟶ b} {d : l ⟶ b}
    (f : k ⟶ l) (hf : f ≫ d = c) (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (map f hf j hj).toOrderHom (vertexEquiv c n x) =
      vertexEquiv d m (f.toOrderHom x.1, j.toOrderHom x.2) := by
  change vertexEquiv d m (f.toOrderHom ((vertexEquiv c n).symm (vertexEquiv c n x)).1,
    j.toOrderHom ((vertexEquiv c n).symm (vertexEquiv c n x)).2) = _
  rw [Equiv.symm_apply_apply]

theorem map_base {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) :
    map f hf j hj ≫ base d m = base c n := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective v
  change (base d m).toOrderHom ((map f hf j hj).toOrderHom (vertexEquiv c n x)) = _
  rw [map_vertexEquiv, base_vertexEquiv, base_vertexEquiv, coeff_eq hf]

theorem slice_map {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) (t : Fin (n.len + 1)) :
    slice c n t ≫ map f hf j hj = f ≫ slice d m (j.toOrderHom t) := by
  ext a : 3
  exact map_vertexEquiv f hf j hj (a, t)

theorem vertical_map {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) (a : Fin (k.len + 1)) :
    vertical c n a ≫ map f hf j hj = j ≫ vertical d m (f.toOrderHom a) := by
  ext t : 3
  exact map_vertexEquiv f hf j hj (a, t)

theorem map_id (c : k ⟶ b) (n : SimplexCategory) :
    map (𝟙 k) (Category.id_comp c) (𝟙 n) (fun _ _ h ↦ h) = 𝟙 (common k n) := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective v
  rw [map_vertexEquiv]
  rfl

theorem map_comp {k' n' : SimplexCategory} {c : k ⟶ b} {d : l ⟶ b} {e : k' ⟶ b}
    (f : k ⟶ l) (g : l ⟶ k') (hf : f ≫ d = c) (hg : g ≫ e = d)
    (j : n ⟶ m) (j' : m ⟶ n') (hj : Function.Injective j.toOrderHom)
    (hj' : Function.Injective j'.toOrderHom) :
    map (f ≫ g) (by rw [Category.assoc, hg, hf]) (j ≫ j') (hj'.comp hj) =
      map f hf j hj ≫ map g hg j' hj' := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective v
  change (map (f ≫ g) _ (j ≫ j') (hj'.comp hj)).toOrderHom (vertexEquiv c n x) =
    (map g hg j' hj').toOrderHom ((map f hf j hj).toOrderHom (vertexEquiv c n x))
  simp only [map_vertexEquiv]
  rfl

end

end DaggerModels.PartII.JTCommonCoefficientParameter
