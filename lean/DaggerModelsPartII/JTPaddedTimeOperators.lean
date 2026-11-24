import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-! The original time ordinal with an extra first and last vertex.
Every simplex operator extends to one preserving those two vertices.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTPaddedTimeOperators

/-- Add one new vertex before and one after the original time simplex. -/
abbrev pad (n : SimplexCategory) : SimplexCategory := ⦋n.len + 2⦌

/-- The original interior time vertices, in order. -/
def inside (n : SimplexCategory) : Fin (n.len + 1) →o Fin ((pad n).len + 1) where
  toFun i := i.castSucc.succ
  monotone' := fun _ _ h ↦ Nat.succ_le_succ h

/-- Extend an interior vertex map using the first and last vertices of its target. -/
def extend {n m : SimplexCategory} (u : Fin (n.len + 1) →o Fin (m.len + 1)) :
    pad n ⟶ m :=
  SimplexCategory.Hom.mk
    ⟨Fin.cases 0 (Fin.lastCases (Fin.last m.len) u), by
      intro i j h
      induction i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          change i.val + 1 ≤ 0 at h
          omega
        | succ j =>
          simp only [Fin.cases_succ]
          induction j using Fin.lastCases with
          | last =>
            rw [Fin.lastCases_last]
            exact Fin.le_last _
          | cast j =>
            induction i using Fin.lastCases with
            | last =>
              change n.len + 1 + 1 ≤ j.val + 1 at h
              omega
            | cast i =>
              simp only [Fin.lastCases_castSucc]
              exact u.monotone (Nat.le_of_succ_le_succ h)⟩

@[simp] theorem extend_first {n m : SimplexCategory} (u : Fin (n.len + 1) →o Fin (m.len + 1)) :
    (extend u : pad n ⟶ m).toOrderHom 0 = 0 := rfl

@[simp] theorem extend_inside {n m : SimplexCategory} (u : Fin (n.len + 1) →o Fin (m.len + 1))
    (i : Fin (n.len + 1)) : (extend u : pad n ⟶ m).toOrderHom (inside n i) = u i := by
  change Fin.cases 0 (Fin.lastCases (Fin.last m.len) u) i.castSucc.succ = u i
  rw [Fin.cases_succ, Fin.lastCases_castSucc]

@[simp] theorem extend_last {n m : SimplexCategory} (u : Fin (n.len + 1) →o Fin (m.len + 1)) :
    (extend u : pad n ⟶ m).toOrderHom (Fin.last (pad n).len) = Fin.last m.len := by
  change Fin.cases 0 (Fin.lastCases (Fin.last m.len) u) (Fin.last (n.len + 1)).succ = Fin.last m.len
  rw [Fin.cases_succ, Fin.lastCases_last]

/-- The two extra vertices and the original interior determine the entire operator. -/
theorem hom_ext {n m : SimplexCategory} {u v : pad n ⟶ m}
    (h₀ : u.toOrderHom 0 = v.toOrderHom 0)
    (hᵢ : ∀ i, u.toOrderHom (inside n i) = v.toOrderHom (inside n i))
    (h₁ : u.toOrderHom (Fin.last (pad n).len) = v.toOrderHom (Fin.last (pad n).len)) : u = v := by
  ext i : 3
  induction i using Fin.cases with
  | zero => exact h₀
  | succ i =>
    induction i using Fin.lastCases with
    | last => exact h₁
    | cast i => exact hᵢ i

/-- Extend an arbitrary simplex operator, retaining both extra vertices. -/
def map {m n : SimplexCategory} (f : m ⟶ n) : pad m ⟶ pad n :=
  extend ((inside n).comp f.toOrderHom)

@[simp] theorem map_first {m n : SimplexCategory} (f : m ⟶ n) :
    (map f).toOrderHom 0 = 0 := extend_first _

@[simp] theorem map_inside {m n : SimplexCategory} (f : m ⟶ n) (i : Fin (m.len + 1)) :
    (map f).toOrderHom (inside m i) = inside n (f.toOrderHom i) := extend_inside _ _

@[simp] theorem map_last {m n : SimplexCategory} (f : m ⟶ n) :
    (map f).toOrderHom (Fin.last (pad m).len) = Fin.last (pad n).len := extend_last _

/-- Padding respects all original simplex operators. -/
def functor : SimplexCategory ⥤ SimplexCategory where
  obj := pad
  map := map
  map_id n := by
    apply hom_ext (n := n)
    · exact map_first _
    · intro i
      exact map_inside _ i
    · exact map_last _
  map_comp {n m l} f g := by
    apply hom_ext (n := n)
    · change (map (f ≫ g)).toOrderHom 0 = (map g).toOrderHom ((map f).toOrderHom 0)
      simp only [map_first]
    · intro i
      change (map (f ≫ g)).toOrderHom (inside n i) =
        (map g).toOrderHom ((map f).toOrderHom (inside n i))
      simp only [map_inside]
      rfl
    · change (map (f ≫ g)).toOrderHom (Fin.last (pad n).len) =
        (map g).toOrderHom ((map f).toOrderHom (Fin.last (pad n).len))
      simp only [map_last]

/-- The edge joining the two extra vertices. -/
def edge (n : SimplexCategory) : ⦋1⦌ ⟶ pad n :=
  SimplexCategory.mkOfLe 0 (Fin.last (pad n).len) (Fin.zero_le _)

theorem edge_map {m n : SimplexCategory} (f : m ⟶ n) :
    edge m ≫ map f = edge n := by
  apply SimplexCategory.Hom.ext_one_left
  · change (map f).toOrderHom 0 = 0
    exact map_first _
  · change (map f).toOrderHom (Fin.last (pad m).len) = Fin.last (pad n).len
    exact map_last _

/-- Collapse the original interior vertices to the first added vertex. -/
def collapse (n : SimplexCategory) : pad n ⟶ ⦋1⦌ :=
  extend (OrderHom.const _ 0)

theorem edge_collapse (n : SimplexCategory) : edge n ≫ collapse n = 𝟙 ⦋1⦌ := by
  apply SimplexCategory.Hom.ext_one_left
  · change (collapse n).toOrderHom 0 = 0
    exact extend_first _
  · change (collapse n).toOrderHom (Fin.last (pad n).len) = Fin.last 1
    exact extend_last _

theorem map_collapse {m n : SimplexCategory} (f : m ⟶ n) :
    map f ≫ collapse n = collapse m := by
  apply hom_ext (n := m)
  · change (collapse n).toOrderHom ((map f).toOrderHom 0) = _
    simp only [map_first, collapse, extend_first]
  · intro i
    change (collapse n).toOrderHom ((map f).toOrderHom (inside m i)) = _
    simp only [map_inside, collapse, extend_inside]
    rfl
  · change (collapse n).toOrderHom ((map f).toOrderHom (Fin.last (pad m).len)) = _
    simp only [map_last, collapse, extend_last]

end DaggerModels.PartII.JTPaddedTimeOperators
