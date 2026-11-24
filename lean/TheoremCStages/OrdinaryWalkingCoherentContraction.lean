import DaggerModelsPartII.JTParameterContraction
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# A coherent directed contraction of the original walking parameter

The codiscrete comparison makes the ordinary interval contraction extend
over the entire groupoid-completed interval. The second factor is the
original walking parameter, so this map can represent a coherent
equivalence arrow after currying against an ordinary Segal target.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory
open DaggerModels.PartII.GroupoidSimplex
open DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.OrdinaryWalkingCoherentContraction

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev comparison : E ≅ codiscreteNerve.obj (Fin 2) :=
  GroupoidSimplex.parameterCodiscreteIso.app ⦋1⦌

private theorem codiscrete_hom_ext {X : SSet.{0}}
    {f g : X ⟶ codiscreteNerve.obj (Fin 2)}
    (h : ∀ x : X.obj (op ⦋0⦌), vertexLabels f x = vertexLabels g x) : f = g := by
  apply NatTrans.ext
  funext n s
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  calc
    ((f.app n s).obj i).as =
        vertexLabels f (X.map ((⦋0⦌ : SimplexCategory).const n.unop i).op s) :=
      (vertexLabels_natural f n s i).symm
    _ = vertexLabels g (X.map ((⦋0⦌ : SimplexCategory).const n.unop i).op s) := h _
    _ = ((g.app n s).obj i).as := vertexLabels_natural g n s i

private theorem vertexLabels_mapOfVertices (X : SSet.{0})
    (φ : X.obj (op ⦋0⦌) → Fin 2) (x : X.obj (op ⦋0⦌)) :
    vertexLabels (mapOfVertices X φ) x = φ x := by
  change φ (X.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op x) = φ x
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

private theorem constantAt_label (i : Fin 2) (x : E.obj (op ⦋0⦌)) :
    vertexLabels
        (JTParameterContraction.constantAt ⦋1⦌ i ≫ comparison.hom) x = i := by
  change vertexLabels
      (mapOfVertices E (fun _ => i) ≫ comparison.inv ≫ comparison.hom) x = i
  rw [Iso.inv_hom_id, Category.comp_id]
  exact vertexLabels_mapOfVertices E (fun _ => i) x

/-- The vertex label of a coherent contraction chooses the source at
time zero and the specified constant vertex at time one. -/
def label (j : Fin 2) (x : (E ⊗ E).obj (op ⦋0⦌)) : Fin 2 :=
  by
    classical
    exact if vertexLabels comparison.hom x.2 = (0 : Fin 2) then
      vertexLabels comparison.hom x.1
    else j

/-- A whole-map contraction with the actual groupoid-completed interval
as its time parameter. -/
def contraction (j : Fin 2) : E ⊗ E ⟶ E :=
  mapOfVertices (E ⊗ E) (label j) ≫ comparison.inv

/-- The actual two vertex slices of the groupoid-time contraction. -/
def slice (i : Fin 2) : E ⟶ E ⊗ E :=
  lift (𝟙 E) (JTParameterContraction.constantAt ⦋1⦌ i)

/-- At the original first vertex, the coherent contraction is identity. -/
theorem contraction_zero (j : Fin 2) :
    slice 0 ≫ contraction j = 𝟙 E := by
  classical
  apply (cancel_mono comparison.hom).mp
  rw [Category.assoc, contraction, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply codiscrete_hom_ext
  intro x
  change (if vertexLabels
      (JTParameterContraction.constantAt ⦋1⦌ 0 ≫ comparison.hom) x = 0 then
      vertexLabels comparison.hom x else j) = vertexLabels comparison.hom x
  rw [constantAt_label]
  rfl

/-- At the second vertex, the coherent contraction is constant at `j`. -/
theorem contraction_one (j : Fin 2) :
    slice 1 ≫ contraction j = JTParameterContraction.constantAt ⦋1⦌ j := by
  classical
  apply (cancel_mono comparison.hom).mp
  rw [Category.assoc, contraction, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply codiscrete_hom_ext
  intro x
  change (if vertexLabels
      (JTParameterContraction.constantAt ⦋1⦌ 1 ≫ comparison.hom) x = 0 then
      vertexLabels comparison.hom x else j) =
    vertexLabels (JTParameterContraction.constantAt ⦋1⦌ j ≫ comparison.hom) x
  rw [constantAt_label, constantAt_label]
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp only [h, ↓reduceIte]

#print axioms contraction_zero
#print axioms contraction_one

end
end DaggerModels.PartII.OrdinaryWalkingCoherentContraction
