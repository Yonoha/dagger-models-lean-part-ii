import DaggerModelsPartII.JTRowGraphRelations
import DaggerModelsPartII.JTRowGraphParameterSupport
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# The canonical representative of an actual JT row graph

First restrict the coefficient and parameter to the used vertices, then
take the Eilenberg--Zilber nondegenerate coefficient. Every coend step
induces an epimorphism between its supports, so uniqueness applies.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTRowGraphNormalForm

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphParameterSupport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev row (W : BiPresheaf) (d : SimplexCategory) :=
  (JTRealizationDiagonal.ordinaryCurry.obj W).obj (op d)

private def verticalOp (d : SimplexCategory) {k l : SimplexCategory} (j : k ⟶ l) :
    (d, k) ⟶ (d, l) :=
  (𝟙 d, j)

private theorem row_map (W : BiPresheaf) (d : SimplexCategory) {k l : SimplexCategory}
    (j : k ⟶ l) (w : W.obj (op (d, l))) :
    (row W d).map j.op w = W.map (verticalOp d j).op w := rfl

variable {W : BiPresheaf} {d : SimplexCategory}

/-- Restrict a row graph to the actual vertices used by its parameter. -/
def support (G : Graph W d) : Graph W d where
  degree := supportOrdinal G.parameter
  coefficient := (row W d).map (inclusion G.parameter).op G.coefficient
  parameter := source G.parameter

/-- The used-vertex restriction is one original vertical coend step. -/
theorem support_step (G : Graph W d) : Step W d (support G) G := by
  obtain ⟨k, w, s⟩ := G
  have h := Step.along (W := W) (d := d) (inclusion s) w (source s)
  rw [source_factor] at h
  exact h

/-- Actual Eilenberg--Zilber data of the whole coefficient. -/
structure Reduction (G : Graph W d) where
  dim : ℕ
  operator : G.degree ⟶ ⦋dim⦌
  epi : Epi operator
  simplex : (row W d).nonDegenerate dim
  fac : G.coefficient = (row W d).map operator.op simplex.val

/-- Use Mathlib's Eilenberg--Zilber decomposition in the fixed row. -/
def reduction (G : Graph W d) : Reduction G :=
  Classical.choice (by
    obtain ⟨k, w, s⟩ := G
    induction k using SimplexCategory.rec with
    | _ n =>
      obtain ⟨m, f, hf, x, hx⟩ := (row W d).exists_nonDegenerate w
      exact ⟨⟨m, f, hf, x, hx⟩⟩)

private def Reduction.graph {G : Graph W d} (r : Reduction G) : Graph W d :=
  ⟨⦋r.dim⦌, r.simplex.val, G.parameter ≫ J.map r.operator⟩

private theorem Reduction.step {G : Graph W d} (r : Reduction G) :
    Step W d G r.graph := by
  obtain ⟨k, w, s⟩ := G
  let v := r.simplex.val
  have h := Step.along (W := W) (d := d) r.operator v s
  have hw : W.map (verticalOp d r.operator).op v = w :=
    ((row_map W d r.operator v).symm.trans r.fac.symm)
  change Step W d ⟨k, W.map (verticalOp d r.operator).op v, s⟩ _ at h
  rw [hw] at h
  exact h

private theorem reduction_graph_epi {k l : SimplexCategory} (j : k ⟶ l) [Epi j]
    (w : W.obj (op (d, l))) (s : SSet.stdSimplex.obj d ⟶ J.obj k)
    (a : Reduction (⟨k, (row W d).map j.op w, s⟩ : Graph W d))
    (b : Reduction (⟨l, w, s ≫ J.map j⟩ : Graph W d)) :
    a.graph = b.graph := by
  obtain ⟨m, f, hf, u, h₁⟩ := a
  obtain ⟨n, g, hg, v, h₂⟩ := b
  change k ⟶ ⦋m⦌ at f
  change l ⟶ ⦋n⦌ at g
  change (row W d).map j.op w = (row W d).map f.op u.val at h₁
  change w = (row W d).map g.op v.val at h₂
  letI := hf
  letI := hg
  have h₃ : (row W d).map j.op w = (row W d).map (j ≫ g).op v.val := by
    rw [op_comp, (row W d).map_comp, CategoryTheory.types_comp_apply]
    exact congrArg ((row W d).map j.op) h₂
  induction k using SimplexCategory.rec with
  | _ z =>
    have hdim := (row W d).unique_nonDegenerate_dim _ f u h₁ (j ≫ g) v h₃
    subst n
    have hsimplex := (row W d).unique_nonDegenerate_simplex _ f u h₁ (j ≫ g) v h₃
    have hop := (row W d).unique_nonDegenerate_map _ f u h₁ (j ≫ g) v h₃
    change Graph.mk ⦋m⦌ u.val (s ≫ J.map f) =
      Graph.mk ⦋m⦌ v.val ((s ≫ J.map j) ≫ J.map g)
    rw [hsimplex, hop, J.map_comp, Category.assoc]

/-- Restrict to the used vertices and then remove coefficient degeneracies. -/
def normal (G : Graph W d) : Graph W d := (reduction (support G)).graph

/-- After restricting to the used vertices, removal of the coefficient
degeneracy is a single vertical coend step. -/
theorem support_to_normal (G : Graph W d) : Step W d (support G) (normal G) :=
  (reduction (support G)).step

theorem normal_coefficient_nonDegenerate (G : Graph W d) :
    (normal G).coefficient ∈ (row W d).nonDegenerate (normal G).degree.len :=
  (reduction (support G)).simplex.property

theorem normal_parameter_surjective (G : Graph W d) :
    Function.Surjective (label (normal G).parameter) := by
  let r := reduction (support G)
  intro i
  obtain ⟨u, hu⟩ := (SimplexCategory.epi_iff_surjective.mp r.epi) i
  obtain ⟨v, hv⟩ := source_vertex_surjective G.parameter u
  refine ⟨v, ?_⟩
  change label (source G.parameter ≫ J.map r.operator) v = i
  rw [label_map, hv]
  exact hu

/-- The two steps of normalization retain the actual raw simplex. -/
theorem normal_value (G : Graph W d) : (normal G).value = G.value :=
  (support_to_normal G).value_eq.symm.trans (support_step G).value_eq

private theorem normal_step {G H : Graph W d} (h : Step W d G H) :
    normal G = normal H := by
  cases h with
  | @along k l j w s =>
    let a := inclusion s
    let b := inclusion (s ≫ J.map j)
    let u := supportMap s j
    let v := (row W d).map b.op w
    letI : Epi u := supportMap_epi s j
    have h₁ : (row W d).map a.op (W.map (verticalOp d j).op w) =
        (row W d).map u.op v := by
      change (row W d).map a.op ((row W d).map j.op w) =
        (row W d).map u.op ((row W d).map b.op w)
      have hc := congrArg (fun g : supportOrdinal s ⟶ l ↦ (row W d).map g.op w)
        (supportMap_inclusion s j)
      simpa only [a, b, u, op_comp, Functor.map_comp, CategoryTheory.types_comp_apply]
        using hc.symm
    have h₂ := source_map s j
    have hl : support (⟨k, W.map (verticalOp d j).op w, s⟩ : Graph W d) =
        ⟨supportOrdinal s, (row W d).map u.op v, source s⟩ := by
      change Graph.mk _ _ _ = _
      rw [h₁]
    have hr : support (⟨l, w, s ≫ J.map j⟩ : Graph W d) =
        ⟨supportOrdinal (s ≫ J.map j), v, source s ≫ J.map u⟩ := by
      change Graph.mk _ _ _ = _
      rw [h₂]
    unfold normal
    erw [hl, hr]
    exact reduction_graph_epi u v (source s) _ _

/-- Equality in the raw realization is precisely equality of canonical
row-graph representatives. This holds in every horizontal degree. -/
theorem value_eq_iff_normal_eq (G H : Graph W d) :
    G.value = H.value ↔ normal G = normal H := by
  constructor
  · intro h
    have he := (value_eq_iff G H).mp h
    clear h
    induction he with
    | rel _ _ h => exact normal_step h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    rw [← normal_value G, ← normal_value H, h]

end

end DaggerModels.PartII.JTRowGraphNormalForm
