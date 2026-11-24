import OriginalFlagVertexSupport

/-!
# The support obstruction in the original necklace flag Hom

Support is the existing quotient-invariant image of the first flag set.
The two faces of any original flag-Hom edge have nested supports. This
rules out a strict edge between two prescribed vertices whose supports
are incomparable, even after any original over-target recoding.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget
open DaggerOriginalFlagFlankification

namespace DaggerModels.PartII.OrderedFlagFaceSupport

noncomputable section

universe u

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

/-- For a one-flag, restricting to a later flag set enlarges its
quotient-invariant original vertex support. -/
theorem faceSupport_le (e : (flagHom X a b).obj (op ⦋1⦌))
    (α β : ⦋0⦌ ⟶ ⦋1⦌)
    (hαβ : α.toOrderHom 0 ≤ β.toOrderHom 0) :
    flagVertexSupport (((flagHom X a b).map α.op) e) ⊆
      flagVertexSupport (((flagHom X a b).map β.op) e) := by
  induction e using Quot.ind with
  | _ p =>
    change
      (fun v : Vertices.{u} p.1.code ↦ vertexImage p.1 v.down) ''
          p.2.chain (α.toOrderHom 0) ⊆
        (fun v : Vertices.{u} p.1.code ↦ vertexImage p.1 v.down) ''
          p.2.chain (β.toOrderHom 0)
    exact Set.image_mono (p.2.chain.monotone hαβ)

/-- The face at vertex zero has support contained in the face at vertex one.
This holds on the actual `RawFlag` colimit quotient, not only a representative. -/
theorem faceSupport_subset (e : (flagHom X a b).obj (op ⦋1⦌)) :
    flagVertexSupport
        ((flagHom X a b).map (SimplexCategory.δ (1 : Fin 2)).op e) ⊆
      flagVertexSupport
        ((flagHom X a b).map (SimplexCategory.δ (0 : Fin 2)).op e) := by
  apply faceSupport_le X a b e
  decide

/-- No original flag-Hom edge can have the specified ordered pair of
incomparable-support vertices as its two faces. -/
theorem no_edge_of_incomparable_support
    (v w : (flagHom X a b).obj (op ⦋0⦌))
    (hvw : ¬ flagVertexSupport v ⊆ flagVertexSupport w)
    (hwv : ¬ flagVertexSupport w ⊆ flagVertexSupport v) :
    ¬ ∃ e : (flagHom X a b).obj (op ⦋1⦌),
        ((flagHom X a b).map (SimplexCategory.δ (1 : Fin 2)).op e = v ∧
          (flagHom X a b).map (SimplexCategory.δ (0 : Fin 2)).op e = w) ∨
        ((flagHom X a b).map (SimplexCategory.δ (1 : Fin 2)).op e = w ∧
          (flagHom X a b).map (SimplexCategory.δ (0 : Fin 2)).op e = v) := by
  rintro ⟨e, h | h⟩
  · exact hvw (by simpa only [h.1, h.2] using faceSupport_subset X a b e)
  · exact hwv (by simpa only [h.1, h.2] using faceSupport_subset X a b e)

end

end DaggerModels.PartII.OrderedFlagFaceSupport
