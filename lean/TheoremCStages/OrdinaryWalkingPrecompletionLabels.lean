import DaggerModelsPartII.GroupoidSimplex
import OrdinaryDiscreteMapping
import Mathlib.CategoryTheory.HomCongr

/-!
# Vertex labels for maps to an existing codiscrete nerve

This exposes the vertex-label equivalence for the literal codiscrete nerve.
It does not construct another nerve or change the walking parameter.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingPrecompletionLabels

open DaggerOriginalCodiscreteNerveInjective

noncomputable section

private theorem hom_ext {T : Type} {X : SSet.{0}}
    {f g : X ⟶ codiscreteNerve.obj T}
    (h : ∀ x : X.obj (op ⦋0⦌), vertexLabels f x = vertexLabels g x) : f = g := by
  apply NatTrans.ext
  funext q s
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  calc
    ((f.app q s).obj i).as =
        vertexLabels f (X.map ((⦋0⦌ : SimplexCategory).const q.unop i).op s) :=
      (vertexLabels_natural f q s i).symm
    _ = vertexLabels g (X.map ((⦋0⦌ : SimplexCategory).const q.unop i).op s) := h _
    _ = ((g.app q s).obj i).as := vertexLabels_natural g q s i

private theorem labels_mapOfVertices {T : Type} (X : SSet.{0})
    (φ : X.obj (op ⦋0⦌) → T) (x : X.obj (op ⦋0⦌)) :
    vertexLabels (mapOfVertices X φ) x = φ x := by
  change φ (X.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op x) = φ x
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- A map into the already defined codiscrete nerve is exactly a vertex labeling. -/
def homEquiv (X : SSet.{0}) (T : Type) :
    (X ⟶ codiscreteNerve.obj T) ≃ (X.obj (op ⦋0⦌) → T) where
  toFun := vertexLabels
  invFun := mapOfVertices X
  left_inv f := hom_ext (fun x ↦ labels_mapOfVertices X (vertexLabels f) x)
  right_inv φ := funext (labels_mapOfVertices X φ)

/-- Vertex labels turn precomposition into ordinary function precomposition. -/
theorem homEquiv_pre {X Y : SSet.{0}} {T : Type}
    (u : X ⟶ Y) (f : Y ⟶ codiscreteNerve.obj T) :
    homEquiv X T (u ≫ f) =
      (homEquiv Y T f) ∘ u.app (op ⦋0⦌) := by
  funext x
  rfl

/-- The original completed simplex is labeled by its finite vertices. -/
def parameterVertexEquiv (q : SimplexCategory) :
    (GroupoidSimplex.parameter.obj q).obj (op ⦋0⦌) ≃ Fin (q.len + 1) :=
  ((GroupoidSimplex.parameterCodiscreteIso.app q).app (op ⦋0⦌)).toEquiv.trans
    { toFun := fun s ↦ (nerveEquiv s).as
      invFun := fun i ↦ nerveEquiv.symm (Codiscrete.mk i)
      left_inv := by
        intro s
        apply nerveEquiv.injective
        simpa only [Equiv.apply_symm_apply] using
          (show Codiscrete.mk (nerveEquiv s).as = nerveEquiv s from rfl)
      right_inv := by
        intro i
        simp only [Equiv.apply_symm_apply] }

/-- A map to the original walking parameter is exactly a binary vertex labeling. -/
def walkingHomEquiv (X : SSet.{0}) :
    (X ⟶ GroupoidSimplex.parameter.obj ⦋1⦌) ≃
      (X.obj (op ⦋0⦌) → Fin 2) :=
  ((Iso.refl X).homCongr (GroupoidSimplex.parameterCodiscreteIso.app ⦋1⦌)).trans
    (homEquiv X (Fin 2))

/-- The walking labels respect precomposition by the entire simplicial map. -/
theorem walkingHomEquiv_pre {X Y : SSet.{0}} (u : X ⟶ Y)
    (f : Y ⟶ GroupoidSimplex.parameter.obj ⦋1⦌) :
    walkingHomEquiv X (u ≫ f) =
      (walkingHomEquiv Y f) ∘ u.app (op ⦋0⦌) := by
  funext x
  change vertexLabels
      (u ≫ f ≫ (GroupoidSimplex.parameterCodiscreteIso.app ⦋1⦌).hom) x =
    vertexLabels (f ≫ (GroupoidSimplex.parameterCodiscreteIso.app ⦋1⦌).hom)
      (u.app (op ⦋0⦌) x)
  rfl

#print axioms homEquiv
#print axioms homEquiv_pre
#print axioms parameterVertexEquiv
#print axioms walkingHomEquiv
#print axioms walkingHomEquiv_pre

end

end DaggerModels.PartII.OrdinaryWalkingPrecompletionLabels
