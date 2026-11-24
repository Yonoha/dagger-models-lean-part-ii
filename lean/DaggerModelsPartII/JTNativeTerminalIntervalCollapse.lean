import ChosenNecklaceCutPushout
import ChosenNecklaceSingleBead
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

/-!
# A cut inside a bead does not give a terminal-interval pushout

The two edges below give the smallest obstruction.  Collapsing the vertices
after the cut identifies a mixed edge with an edge in the retained interval.
The proposed degreewise fiber description therefore fails already for one
ordinary two-simplex.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativeTerminalIntervalCollapse

noncomputable section

/-- The monotone vertex clamp $0 \mapsto 0$, $1 \mapsto 1$, $2 \mapsto 1$. -/
def clamp : ⦋2⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ ⟨min i.val 1, by
        change min i.val 1 < 1 + 1
        omega⟩, by
      intro i j hij
      change i.val ≤ j.val at hij
      change min i.val 1 ≤ min j.val 1
      omega⟩

/-- The edge from vertex zero to vertex one of the full two-simplex. -/
def edge01 : (Δ[2] : SSet.{0}).obj (op ⦋1⦌) :=
  SSet.stdSimplex.objMk
    ⟨fun i ↦ ⟨i.val, by
        have hi := i.isLt
        change i.val < 1 + 1 at hi
        change i.val < 2 + 1
        omega⟩, by
      intro i j hij
      change i.val ≤ j.val at hij
      exact hij⟩

/-- The mixed edge from vertex zero to vertex two. -/
def edge02 : (Δ[2] : SSet.{0}).obj (op ⦋1⦌) :=
  SSet.stdSimplex.objMk
    ⟨fun i ↦ ⟨2 * i.val, by
        have hi := i.isLt
        change i.val < 1 + 1 at hi
        change 2 * i.val < 2 + 1
        omega⟩, by
      intro i j hij
      change i.val ≤ j.val at hij
      change 2 * i.val ≤ 2 * j.val
      omega⟩

theorem edges_distinct : edge01 ≠ edge02 := by
  intro h
  have hh := congrArg (fun x : (Δ[2] : SSet.{0}).obj (op ⦋1⦌) ↦ x ⟨1, by omega⟩) h
  have hv := congrArg Fin.val hh
  norm_num [edge01, edge02] at hv

theorem edge01_starts_before_cut : edge01 ⟨0, by omega⟩ < (1 : Fin 3) := by
  decide

theorem edge02_starts_before_cut : edge02 ⟨0, by omega⟩ < (1 : Fin 3) := by
  decide

/-- The pointwise clamp has a nontrivial fiber containing mixed simplices. -/
theorem mixed_edges_same_clamp :
    (SSet.stdSimplex.map clamp).app (op ⦋1⦌) edge01 =
      (SSet.stdSimplex.map clamp).app (op ⦋1⦌) edge02 := by
  ext i
  fin_cases i <;> rfl

/-- The same obstruction occurs in the actual single-bead necklace. -/
def necklaceEdge01 : (single 2).toSSet.obj (op ⦋1⦌) :=
  (singleIso 2).inv.app _ edge01

def necklaceEdge02 : (single 2).toSSet.obj (op ⦋1⦌) :=
  (singleIso 2).inv.app _ edge02

theorem necklace_edges_distinct : necklaceEdge01 ≠ necklaceEdge02 := by
  intro h
  apply edges_distinct
  have hh := congrArg ((singleIso 2).hom.app (op ⦋1⦌)) h
  simpa [necklaceEdge01, necklaceEdge02] using hh

/-- The coordinate clamp as an actual simplicial map between native single-bead necklaces. -/
def necklaceClamp : (single 2).toSSet ⟶ (single 1).toSSet :=
  (singleIso 2).hom ≫ SSet.stdSimplex.map clamp ≫ (singleIso 1).inv

theorem necklace_mixed_edges_same_clamp :
    necklaceClamp.app (op ⦋1⦌) necklaceEdge01 =
      necklaceClamp.app (op ⦋1⦌) necklaceEdge02 := by
  simp only [necklaceClamp, necklaceEdge01]
  exact congrArg ((singleIso 1).inv.app (op ⦋1⦌)) mixed_edges_same_clamp

private theorem not_pushout_of_mixed_fiber {A B C D : Type}
    (f : A ⟶ B) (g : A ⟶ C) (r : B ⟶ D) (s : C ⟶ D)
    (x y : B) (hx : x ∉ Set.range f) (hxy : r x = r y) (hne : x ≠ y) :
    ¬ IsPushout f g r s := by
  classical
  intro hp
  let p : B ⟶ Bool := fun z ↦ decide (z = x)
  let q : C ⟶ Bool := fun _ ↦ false
  have w : f ≫ p = g ≫ q := by
    funext a
    have hax : f a ≠ x := by
      intro h
      exact hx ⟨a, h⟩
    simp [p, q, hax]
  obtain ⟨d, hd, _⟩ := hp.exists_desc p q w
  have hdx : d (r x) = p x := congrFun hd x
  have hdy : d (r y) = p y := congrFun hd y
  have hp' : p x = p y := by
    calc
      p x = d (r x) := hdx.symm
      _ = d (r y) := congrArg d hxy
      _ = p y := hdy
  simp [p, Ne.symm hne] at hp'

private def cut : Fin ((single 2).len + 1) := ⟨1, by decide⟩

theorem necklace_edge01_not_right_range :
    necklaceEdge01 ∉ Set.range ((cutRightι.{0} (single 2) cut).app (op ⦋1⦌)) := by
  rintro ⟨y, hy⟩
  have h := congrArg (fun z : (single 2).toSSet.obj (op ⦋1⦌) ↦
    (single 2).inclusion.app (op ⦋1⦌) z ⟨0, by omega⟩) hy
  change (single 2).inclusion.app _
      ((intervalι (single 2) cut (Fin.last 2) (Fin.le_last cut)).app _ y) 0 =
    (single 2).inclusion.app _ necklaceEdge01 0 at h
  rw [intervalι_apply] at h
  have hb := (intervalEmbedding_bounds (single 2) cut (Fin.last 2) (Fin.le_last cut)
    ((cutRight (single 2) cut).inclusion.app (op ⦋1⦌) y 0)).1
  have hz : (single 2).inclusion.app (op ⦋1⦌) necklaceEdge01 0 = 0 := by
    rw [← singleIso_hom]
    change edge01 0 = 0
    rfl
  rw [hz] at h
  have hc : cut ≤ (0 : Fin 3) := by rw [← h]; exact hb
  exact (by decide : ¬ cut ≤ (0 : Fin 3)) hc

/-- No choice of the other two legs makes this clamp a pushout of the terminal interval. -/
theorem necklace_clamp_not_pushout {C : SSet.{0}}
    (g : (cutRight (single 2) cut).toSSet ⟶ C)
    (s : C ⟶ (single 1).toSSet) :
    ¬ IsPushout (cutRightι.{0} (single 2) cut) g necklaceClamp s := by
  intro hp
  have hd := IsPushout.map ((evaluation SimplexCategoryᵒᵖ (Type)).obj (op ⦋1⦌)) hp
  change IsPushout ((cutRightι (single 2) cut).app (op ⦋1⦌))
    (g.app (op ⦋1⦌)) (necklaceClamp.app (op ⦋1⦌))
    (s.app (op ⦋1⦌)) at hd
  exact (not_pushout_of_mixed_fiber _ _ _ _ necklaceEdge01 necklaceEdge02
    necklace_edge01_not_right_range necklace_mixed_edges_same_clamp
    necklace_edges_distinct) hd

end

end DaggerModels.PartII.JTNativeTerminalIntervalCollapse
