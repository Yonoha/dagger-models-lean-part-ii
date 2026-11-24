import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Descent along an increasing exhaustive sequence of simplicial subcomplexes

The pinned subcomplex multicoequalizer identifies the supremum of a family
as the colimit of its members and their pairwise intersections. For a
monotone sequence indexed by natural numbers, each intersection is the
member at the minimum index. Compatible maps therefore descend to the
whole simplicial set when the sequence covers it.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits

universe u

namespace DaggerModels.PartII.NatSubcomplexGluing

noncomputable section

variable {X Y : SSet.{u}} (S : ℕ → X.Subcomplex)
  (hmono : Monotone S) (hcover : (⨆ n, S n) = ⊤)

private def diagram : SSet.Subcomplex.MulticoequalizerDiagram
    (⊤ : X.Subcomplex) S (fun i j ↦ S (min i j)) where
  iSup_eq := hcover
  eq_inf i j := by
    rcases le_total i j with hij | hji
    · rw [min_eq_left hij, inf_eq_left.mpr (hmono hij)]
    · rw [min_eq_right hji, inf_eq_right.mpr (hmono hji)]

variable (f : ∀ n, (S n : SSet.{u}) ⟶ Y)
  (hcompat : ∀ n m (h : n ≤ m),
    SSet.Subcomplex.homOfLE (hmono h) ≫ f m = f n)

private def cofork : Multicofork ((diagram S hmono hcover).multispanIndex.map
    SSet.Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ Y f (fun ⟨i, j⟩ ↦ by
    let hi : S (min i j) ≤ S i := hmono (min_le_left i j)
    let hj : S (min i j) ≤ S j := hmono (min_le_right i j)
    change SSet.Subcomplex.homOfLE hi ≫ f i =
      SSet.Subcomplex.homOfLE hj ≫ f j
    exact (hcompat (min i j) i (min_le_left i j)).trans
      (hcompat (min i j) j (min_le_right i j)).symm)

/-- The actual map from the entire simplicial set induced by compatible
maps on an exhaustive increasing sequence of subcomplexes. -/
def desc : X ⟶ Y :=
  (SSet.Subcomplex.topIso X).inv ≫
    (diagram S hmono hcover).isColimit.desc (cofork S hmono hcover f hcompat)

/-- The descended map has the exact prescribed restriction at every stage. -/
theorem ι_desc (n : ℕ) : (S n).ι ≫ desc S hmono hcover f hcompat = f n := by
  let htop : S n ≤ (⊤ : X.Subcomplex) := le_top
  have hι : (S n).ι ≫ (SSet.Subcomplex.topIso X).inv =
      SSet.Subcomplex.homOfLE htop := by
    calc
      (S n).ι ≫ (SSet.Subcomplex.topIso X).inv =
          (SSet.Subcomplex.homOfLE htop ≫
            (SSet.Subcomplex.topIso X).hom) ≫
              (SSet.Subcomplex.topIso X).inv := by
        rw [SSet.Subcomplex.topIso_hom, SSet.Subcomplex.homOfLE_ι]
      _ = SSet.Subcomplex.homOfLE htop := by
        rw [Category.assoc, (SSet.Subcomplex.topIso X).hom_inv_id, Category.comp_id]
  have hf := (diagram S hmono hcover).isColimit.fac
    (cofork S hmono hcover f hcompat) (.right n)
  change SSet.Subcomplex.homOfLE htop ≫
    (diagram S hmono hcover).isColimit.desc (cofork S hmono hcover f hcompat) =
      f n at hf
  change (S n).ι ≫ ((SSet.Subcomplex.topIso X).inv ≫
    (diagram S hmono hcover).isColimit.desc (cofork S hmono hcover f hcompat)) =
      f n
  rw [← Category.assoc, hι]
  exact hf

#print axioms desc
#print axioms ι_desc

end

end DaggerModels.PartII.NatSubcomplexGluing
