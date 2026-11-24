import DaggerModelsPartII.GroupoidSimplex
import OriginalCounitRightConeRelativeHomotopyEndpoints

/-!
# A directed contraction of the actual JT groupoid parameter

The codiscrete nerve receives every function on vertices.  Apply this to
the vertices of the Cartesian cylinder, selecting the original vertex at
time zero and a chosen vertex at time one.  The resulting map is transported
back along the installed natural isomorphism from the actual groupoid
parameter to the codiscrete nerve.  No dagger homotopy or weak-equivalence
assertion is made here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTParameterContraction

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective
open DaggerOriginalCounitRightConeRelativeHomotopy

noncomputable section

private def comparison (k : SimplexCategory) :
    parameter.obj k ≅ codiscreteNerve.obj (Fin (k.len + 1)) :=
  parameterCodiscreteIso.app k

/-- The chosen vertex of the actual groupoid-completed parameter. -/
def parameterVertex (k : SimplexCategory) (j : Fin (k.len + 1)) :
    (Δ[0] : SSet.{0}) ⟶ parameter.obj k :=
  mapOfVertices (Δ[0] : SSet.{0}) (fun _ => j) ≫ (comparison k).inv

/-- The actual parameter map constant at the chosen vertex. -/
def constantAt (k : SimplexCategory) (j : Fin (k.len + 1)) :
    parameter.obj k ⟶ parameter.obj k :=
  mapOfVertices (parameter.obj k) (fun _ => j) ≫ (comparison k).inv

/-- The label of a vertex of the cylinder: the original label at time zero,
and the chosen label at time one. -/
private def contractionLabel (k : SimplexCategory) (j : Fin (k.len + 1))
    (x : (parameter.obj k ⊗ (Δ[1] : SSet.{0})).obj (op ⦋0⦌)) :
    Fin (k.len + 1) :=
  if x.2 0 = (0 : Fin 2) then
    vertexLabels (comparison k).hom x.1
  else j

/-- The directed cylinder map on the **actual** `parameter.obj k`, obtained
by transporting the vertexwise codiscrete map through its chosen isomorphism. -/
def contraction (k : SimplexCategory) (j : Fin (k.len + 1)) :
    parameter.obj k ⊗ (Δ[1] : SSet.{0}) ⟶ parameter.obj k :=
  mapOfVertices (parameter.obj k ⊗ (Δ[1] : SSet.{0}))
    (contractionLabel k j) ≫ (comparison k).inv

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

private theorem contraction_cod_time_zero
    (k : SimplexCategory) (j : Fin (k.len + 1)) :
    timeSlice (parameter.obj k) 0 ≫
      mapOfVertices (parameter.obj k ⊗ (Δ[1] : SSet.{0}))
        (contractionLabel k j) = (comparison k).hom := by
  apply codiscrete_hom_ext
  intro x
  change contractionLabel k j ((timeSlice (parameter.obj k) 0).app (op ⦋0⦌) x) =
    vertexLabels (comparison k).hom x
  simp only [contractionLabel, timeSlice]
  rfl

private theorem contraction_cod_time_one
    (k : SimplexCategory) (j : Fin (k.len + 1)) :
    timeSlice (parameter.obj k) 1 ≫
      mapOfVertices (parameter.obj k ⊗ (Δ[1] : SSet.{0}))
        (contractionLabel k j) =
      mapOfVertices (parameter.obj k) (fun _ => j) := by
  apply codiscrete_hom_ext
  intro x
  change contractionLabel k j ((timeSlice (parameter.obj k) 1).app (op ⦋0⦌) x) = j
  simp only [contractionLabel, timeSlice]
  rfl

/-- The zero-time slice of the directed contraction is exactly the identity. -/
theorem contraction_time_zero (k : SimplexCategory) (j : Fin (k.len + 1)) :
    timeSlice (parameter.obj k) 0 ≫ contraction k j =
      𝟙 (parameter.obj k) := by
  change (timeSlice (parameter.obj k) 0 ≫
    mapOfVertices (parameter.obj k ⊗ (Δ[1] : SSet.{0}))
      (contractionLabel k j)) ≫ (comparison k).inv = _
  rw [contraction_cod_time_zero, Iso.hom_inv_id]

/-- The one-time slice is the actual parameter map constant at `j`. -/
theorem contraction_time_one (k : SimplexCategory) (j : Fin (k.len + 1)) :
    timeSlice (parameter.obj k) 1 ≫ contraction k j = constantAt k j := by
  change (timeSlice (parameter.obj k) 1 ≫
    mapOfVertices (parameter.obj k ⊗ (Δ[1] : SSet.{0}))
      (contractionLabel k j)) ≫ (comparison k).inv = _
  rw [contraction_cod_time_one]
  rfl

end

end DaggerModels.PartII.JTParameterContraction
