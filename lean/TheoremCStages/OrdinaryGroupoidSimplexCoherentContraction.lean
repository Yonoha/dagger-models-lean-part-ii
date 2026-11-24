import OrdinaryWalkingCoherentVertexCalibration
import DaggerModelsPartII.JTCodiscreteParameterPairing
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Coherent contraction of every original groupoid simplex

The time parameter is always the original `GroupoidSimplex.parameter.obj ⦋1⦌`.
At time zero this is the identity of `parameter.obj k`; at time one it is
the original `JTParameterContraction.constantAt k j`. The two time slices
use exactly the vertices of the original simplex unit. No statement about
the Rezk completion or Dwyer–Kan equivalences is made here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory
open DaggerModels.PartII.GroupoidSimplex
open DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexCoherentContraction

noncomputable section

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k
private abbrev comparison (k : SimplexCategory) :
    E k ≅ codiscreteNerve.obj (Fin (k.len + 1)) :=
  GroupoidSimplex.parameterCodiscreteIso.app k

private theorem codiscrete_hom_ext {T : Type} {X : SSet.{0}}
    {f g : X ⟶ codiscreteNerve.obj T}
    (h : ∀ x : X.obj (op ⦋0⦌), vertexLabels f x = vertexLabels g x) :
    f = g := by
  apply NatTrans.ext
  funext n s
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  calc
    ((f.app n s).obj i).as =
        vertexLabels f (X.map ((⦋0⦌ : SimplexCategory).const n.unop i).op s) :=
      (vertexLabels_natural f n s i).symm
    _ = vertexLabels g (X.map ((⦋0⦌ : SimplexCategory).const n.unop i).op s) :=
      h _
    _ = ((g.app n s).obj i).as := vertexLabels_natural g n s i

private theorem vertexLabels_mapOfVertices {T : Type} (X : SSet.{0})
    (φ : X.obj (op ⦋0⦌) → T) (x : X.obj (op ⦋0⦌)) :
    vertexLabels (mapOfVertices X φ) x = φ x := by
  change φ (X.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op x) = φ x
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

private theorem constantAt_label (k : SimplexCategory)
    (j : Fin (k.len + 1)) (x : (E k).obj (op ⦋0⦌)) :
    vertexLabels
        (JTParameterContraction.constantAt k j ≫ (comparison k).hom) x = j := by
  change vertexLabels
      (mapOfVertices (E k) (fun _ => j) ≫
        (comparison k).inv ≫ (comparison k).hom) x = j
  rw [Iso.inv_hom_id, Category.comp_id]
  exact vertexLabels_mapOfVertices (E k) (fun _ => j) x

private theorem constant_vertex_map {T : Type} (X : SSet.{0}) (j : T) :
    mapOfVertices X (fun _ => j) =
      SSet.stdSimplex.isTerminalObj₀.from X ≫
        mapOfVertices (Δ[0] : SSet.{0}) (fun _ => j) := by
  apply NatTrans.ext
  funext q x
  apply nerve.ext_of_isThin
  funext a
  apply Codiscrete.ext
  rfl

/-- The actual constant-at-vertex map factors through the original
vertex for every groupoid-completed simplex. -/
theorem constantAt_vertex (k : SimplexCategory) (j : Fin (k.len + 1)) :
    JTParameterContraction.constantAt k j =
      SSet.stdSimplex.isTerminalObj₀.from (E k) ≫
        JTParameterContraction.parameterVertex k j := by
  dsimp only [JTParameterContraction.constantAt,
    JTParameterContraction.parameterVertex]
  rw [constant_vertex_map, Category.assoc]

/-- The time-vertex map has source `E[k]` and target the fixed `E[1]`. -/
def timeConstant (k : SimplexCategory) (i : Fin 2) : E k ⟶ E ⦋1⦌ :=
  mapOfVertices (E k) (fun _ => i) ≫ (comparison ⦋1⦌).inv

private theorem timeConstant_label (k : SimplexCategory) (i : Fin 2)
    (x : (E k).obj (op ⦋0⦌)) :
    vertexLabels (timeConstant k i ≫ (comparison ⦋1⦌).hom) x = i := by
  change vertexLabels
      (mapOfVertices (E k) (fun _ => i) ≫
        (comparison ⦋1⦌).inv ≫ (comparison ⦋1⦌).hom) x = i
  rw [Iso.inv_hom_id, Category.comp_id]
  exact vertexLabels_mapOfVertices (E k) (fun _ => i) x

private theorem timeConstant_vertex (k : SimplexCategory) (i : Fin 2) :
    timeConstant k i =
      SSet.stdSimplex.isTerminalObj₀.from (E k) ≫
        JTParameterContraction.parameterVertex ⦋1⦌ i := by
  dsimp only [timeConstant, JTParameterContraction.parameterVertex]
  rw [constant_vertex_map, Category.assoc]
  rfl

/-- At each actual zero-simplex, preserve the original vertex at time
zero and send it to the specified vertex at time one. -/
def label (k : SimplexCategory) (j : Fin (k.len + 1))
    (x : (E k ⊗ E ⦋1⦌).obj (op ⦋0⦌)) : Fin (k.len + 1) :=
  by
    classical
    exact if vertexLabels (comparison ⦋1⦌).hom x.2 = (0 : Fin 2) then
      vertexLabels (comparison k).hom x.1
    else j

/-- The coherent contraction with the original groupoid-completed
one-simplex as its time parameter. -/
def contraction (k : SimplexCategory) (j : Fin (k.len + 1)) :
    E k ⊗ E ⦋1⦌ ⟶ E k :=
  mapOfVertices (E k ⊗ E ⦋1⦌) (label k j) ≫ (comparison k).inv

/-- The two literal time slices of the same groupoid interval. -/
def slice (k : SimplexCategory) (i : Fin 2) : E k ⟶ E k ⊗ E ⦋1⦌ :=
  lift (𝟙 (E k)) (timeConstant k i)

/-- The time-zero slice recovers the identity of the whole `E[k]`. -/
theorem contraction_zero (k : SimplexCategory) (j : Fin (k.len + 1)) :
    slice k 0 ≫ contraction k j = 𝟙 (E k) := by
  classical
  apply (cancel_mono (comparison k).hom).mp
  rw [Category.assoc, contraction, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  apply codiscrete_hom_ext
  intro x
  change (if vertexLabels
      (timeConstant k 0 ≫ (comparison ⦋1⦌).hom) x = 0 then
      vertexLabels (comparison k).hom x else j) = vertexLabels (comparison k).hom x
  rw [timeConstant_label]
  rfl

/-- The time-one slice is the original constant-at-`j` map on `E[k]`. -/
theorem contraction_one (k : SimplexCategory) (j : Fin (k.len + 1)) :
    slice k 1 ≫ contraction k j = JTParameterContraction.constantAt k j := by
  classical
  apply (cancel_mono (comparison k).hom).mp
  rw [Category.assoc, contraction, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  apply codiscrete_hom_ext
  intro x
  change (if vertexLabels
      (timeConstant k 1 ≫ (comparison ⦋1⦌).hom) x = 0 then
      vertexLabels (comparison k).hom x else j) =
    vertexLabels (JTParameterContraction.constantAt k j ≫ (comparison k).hom) x
  rw [timeConstant_label, constantAt_label]
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp only [h, ↓reduceIte]

/-- The general slice is the right-unitor inclusion at the checked
original groupoid-parameter vertex. -/
theorem slice_vertex (k : SimplexCategory) (i : Fin 2) :
    slice k i =
      (SSet.stdSimplex.rightUnitor (E k)).inv ≫
        E k ◁ JTParameterContraction.parameterVertex ⦋1⦌ i := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · rfl
  · have h := congrFun (NatTrans.congr_app (timeConstant_vertex k i) q) x
    exact h

/-- The same slice uses precisely the original directed simplex-unit
vertex, with no replacement of the time parameter. -/
theorem slice_simplexUnit_vertex (k : SimplexCategory) (i : Fin 2) :
    slice k i =
      (SSet.stdSimplex.rightUnitor (E k)).inv ≫
        E k ◁
          (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) ≫
            JTCylinderCEComparison.simplexUnit.app ⦋1⦌) := by
  rw [OrdinaryWalkingCoherentVertexCalibration.simplexUnit_vertex]
  exact slice_vertex k i

/-- At `k=1`, the time slices are the previously checked literal slices. -/
theorem slice_one_eq_checked (i : Fin 2) :
    slice ⦋1⦌ i = OrdinaryWalkingCoherentContraction.slice i := rfl

#print axioms contraction_zero
#print axioms contraction_one
#print axioms constantAt_vertex
#print axioms slice_vertex
#print axioms slice_simplexUnit_vertex
#print axioms slice_one_eq_checked

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexCoherentContraction
