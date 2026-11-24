import DaggerModelsPartII.JTVariableFixedLiftChoiceDiagram

/-! Natural sections of variable fixed-square lift spaces from exact lift families. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalClosed DaggerModels

namespace DaggerModels.PartII.JTVariableFixedLiftSections

open JTVariableFixedLiftChoiceDiagram

noncomputable section

variable {I : Type} [SmallCategory I] (D : Diagram I)

/-- An objectwise exact lift with the mixed variance required by the diagram. -/
structure LiftFamily where
  lift : ∀ a : I, D.domain.obj a ⟶ D.values.obj (op a)
  support : ∀ a : I, D.incl.app a ≫ lift a = D.onSupport a
  boundary : ∀ a : I,
    lift a ≫ D.restriction.app (op a) = D.base a
  naturality : ∀ {a b : I} (f : a ⟶ b),
    D.domain.map f ≫ lift b ≫ D.values.map f.op = lift a

/-- An exact lift is literally a vertex of its full fixed-square fiber. -/
def vertex (c : LiftFamily D) (a : I) :
    (choices D).obj (op a) |>.obj (op ⦋0⦌) :=
  ⟨SSet.ihom₀Equiv.symm (c.lift a),
    (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (square D a) (c.lift a)).2 ⟨c.support a, c.boundary a⟩⟩

theorem vertex_value (c : LiftFamily D) (a : I) :
    SSet.ihom₀Equiv (vertex D c a).val = c.lift a :=
  Equiv.apply_symm_apply _ _

/-- Restriction carries the selected lift to the exact selected lift. -/
theorem vertex_restrict (c : LiftFamily D) {a b : I} (f : a ⟶ b) :
    ((choices D).map f.op).app (op ⦋0⦌) (vertex D c b) =
      vertex D c a := by
  apply Subtype.ext
  apply SSet.ihom₀Equiv.injective
  change SSet.ihom₀Equiv
      (((JTVariableFixedLiftSpaceMap.mapSquare (square D b) (square D a)
        (D.support.map f) (D.domain.map f) (D.values.map f.op)
        (D.boundary.map f.op) (D.incl.naturality f) (D.onSupport_map f)
        (D.restriction.naturality f.op).symm (D.base_map f)).app _
        (vertex D c b)).val) =
      SSet.ihom₀Equiv (vertex D c a).val
  rw [JTVariableFixedLiftSpaceMap.mapSquare_zero, vertex_value,
    vertex_value]
  exact c.naturality f

/-- A family of exact natural lifts gives a natural point in every full
choice space, without choosing any new lift. -/
def sectionOfLifts (c : LiftFamily D) :
    (Functor.const Iᵒᵖ).obj (SSet.stdSimplex.obj ⦋0⦌) ⟶ choices D where
  app a := SSet.yonedaEquiv.symm (vertex D c a.unop)
  naturality {a b} f := by
    simp only [Functor.const_obj_map]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_symm_comp]
    exact (vertex_restrict D c f.unop).symm

theorem sectionOfLifts_vertex (c : LiftFamily D) (a : I) :
    SSet.yonedaEquiv ((sectionOfLifts D c).app (op a)) =
      vertex D c a := by
  simp [sectionOfLifts]

end
end DaggerModels.PartII.JTVariableFixedLiftSections
