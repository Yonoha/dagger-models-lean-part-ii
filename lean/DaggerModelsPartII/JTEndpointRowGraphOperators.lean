import DaggerModelsPartII.JTEndpointRowGraphResolution
import DaggerModelsPartII.JTRowGraphNormalizationDiagram

/-! The actual endpoint squares commute with independent mixed graph operators. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointRowGraphOperators

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice JTEndpointRowGraphResolution JTRowGraphNormalizationDiagram
open JTRowGraphRelations JTRowGraphCategory

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (m : SimplexCategory) := SSet.stdSimplex.{0}.obj m
private abbrev rows (W : Source) := JTRealizationDiagonal.ordinaryCurry.obj (ordinaryInput.obj W)

variable {W : Source} {d : ℕ} {q : Δ ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}

/-- The horizontal degree of a representative is the source of its operator. -/
abbrev horizontalDegree (A : Resolution q) : SimplexCategory := A.base.unop.left.obj

/-- The unchanged coefficient graph over the horizontal source. -/
abbrev graph (A : Resolution q) : JTRowGraphFiber.Fiber (value q A.base.unop) := A.fiber.unop

/-- The vertical operator of an arrow into the large graph's horizontal restriction. -/
abbrev operator {A B : Resolution q} (f : A ⟶ B) :
    (graph B).obj.degree ⟶ (graph A).obj.degree := f.fiber.unop.hom.operator

private theorem operator_eqToHom {m : SimplexCategory}
    {s : Δ m ⟶ realization.obj (ordinaryInput.obj W)} {P Q : JTRowGraphFiber.Fiber s}
    (h : P = Q) : ((eqToHom h : P ⟶ Q).hom).operator =
      eqToHom (congrArg (fun G ↦ G.obj.degree) h) := by
  cases h
  simp
  rfl

theorem operator_id (A : Resolution q) : operator (𝟙 A) = 𝟙 (graph A).obj.degree := by
  rw [operator, Grothendieck.id_fiber, eqToHom_unop, operator_eqToHom]
  exact eqToHom_refl (graph A).obj.degree _

theorem operator_comp {A B C : Resolution q} (f : A ⟶ B) (g : B ⟶ C) :
    operator (f ≫ g) = operator g ≫ operator f := by
  unfold operator
  rw [Grothendieck.comp_fiber, unop_comp, unop_comp, eqToHom_unop]
  let HS := JTRowGraphFiber.Fiber (value q C.base.unop)
  have hOp {P Q R : HS} (a : P ⟶ Q) (b : Q ⟶ R) :
      ((a ≫ b).hom).operator = a.hom.operator ≫ b.hom.operator := rfl
  simp only [hOp, operator_eqToHom]
  exact Category.comp_id _

private theorem vertex_map {a b : SimplexCategory} (u : a ⟶ b) (i : Fin (a.len + 1)) :
    vertex a i ≫ SSet.stdSimplex.map u = vertex b (u.toOrderHom i) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]

/-- The simplex vertex chosen by the mixed operator is the chosen vertex of the large graph. -/
theorem markedVertex_map {A B : Resolution q} (f : A ⟶ B)
    (i : Fin ((horizontalDegree B).len + 1)) :
    vertex (graph B).obj.degree
      (graphIndex (horizontalDegree B) (graph B).obj.degree (graph B).obj.parameter i) ≫
        SSet.stdSimplex.map (operator f) =
      vertex (graph A).obj.degree
        (graphIndex (horizontalDegree A) (graph A).obj.degree (graph A).obj.parameter
          (f.base.unop.left.1.toOrderHom i)) := by
  let u : horizontalDegree B ⟶ horizontalDegree A := f.base.unop.left.1
  let j := operator f
  have hpar : (graph B).obj.parameter ≫ GroupoidSimplex.parameter.map j =
      SSet.stdSimplex.map u ≫ (graph A).obj.parameter := f.fiber.unop.hom.parameter
  rw [vertex_map]
  have h := JTMixedGraphEdgeFamilyReindex.graphIndex_reindex (d := (horizontalDegree B).len) j (graph B).obj.parameter i
  rw [hpar] at h
  congr 1
  unfold graphIndex at h ⊢
  rw [← Category.assoc, vertex_map] at h
  exact h.symm

/-- The Yoneda realization of the unchanged row coefficient. -/
abbrev graphCoefficient (A : Resolution q) :
    Δ (graph A).obj.degree ⟶ row W (horizontalDegree A) :=
  coefficient (d := (horizontalDegree A).len) (graph A)

/-- Evaluation of the coefficient at every horizontal vertex commutes with the mixed operator. -/
theorem coefficientAtVertex_map {A B : Resolution q} (f : A ⟶ B)
    (i : Fin ((horizontalDegree B).len + 1)) :
    SSet.stdSimplex.map (operator f) ≫ graphCoefficient A ≫
        rowVertex W (horizontalDegree A) (f.base.unop.left.1.toOrderHom i) =
      graphCoefficient B ≫ rowVertex W (horizontalDegree B) i := by
  let u : horizontalDegree B ⟶ horizontalDegree A := f.base.unop.left.1
  let j := operator f
  let ρ : row W (horizontalDegree A) ⟶ row W (horizontalDegree B) := (rows W).map u.op
  let cA : (row W (horizontalDegree A)).obj (op (graph A).obj.degree) :=
    (graph A).obj.coefficient
  let c : (row W (horizontalDegree B)).obj (op (graph A).obj.degree) := ρ.app _ cA
  have h : (row W (horizontalDegree B)).map j.op c = (graph B).obj.coefficient :=
    f.fiber.unop.hom.coefficient
  have hF : SSet.stdSimplex.map j ≫ (graphCoefficient A ≫ ρ) = graphCoefficient B :=
    calc
      _ = SSet.stdSimplex.map j ≫ SSet.yonedaEquiv.symm c :=
        congrArg (SSet.stdSimplex.map j ≫ ·)
          (SSet.yonedaEquiv_symm_comp cA ρ)
      _ = SSet.yonedaEquiv.symm ((row W (horizontalDegree B)).map j.op c) :=
        (SSet.yonedaEquiv_symm_map j c).symm
      _ = _ := congrArg (SSet.yonedaEquiv (X := row W (horizontalDegree B))
        (n := (graph B).obj.degree)).symm h
  have hV : ρ ≫ rowVertex W (horizontalDegree B) i =
      rowVertex W (horizontalDegree A) (u.toOrderHom i) := by
    unfold ρ rowVertex
    rw [← Functor.map_comp, ← op_comp, SimplexCategory.const_comp]
  change SSet.stdSimplex.map j ≫ graphCoefficient A ≫
    rowVertex W (horizontalDegree A) (u.toOrderHom i) = _
  rw [← hV, ← Category.assoc (graphCoefficient A), ← Category.assoc, hF]

/-- Taking the raw realization along the horizontal operator also preserves its marked vertex. -/
theorem rawVertex_restrict (A : Resolution q) (i : Fin ((horizontalDegree A).len + 1)) :
    vertex (horizontalDegree A) i ≫ value q A.base.unop =
      vertex ⦋d⦌ (A.base.unop.hom.1.toOrderHom i) ≫ q := by
  change vertex (horizontalDegree A) i ≫ SSet.stdSimplex.map A.base.unop.hom.1 ≫ q = _
  rw [← Category.assoc, vertex_map]
  rfl

end
end DaggerModels.PartII.JTEndpointRowGraphOperators
