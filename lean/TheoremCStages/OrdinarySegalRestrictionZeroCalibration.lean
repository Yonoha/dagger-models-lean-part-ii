import OrdinarySegalCoherentEdgeNaturality

/-!
# Calibrating the restriction at the original zero-simplex

Evaluation of the existing limit restriction at its identity simplex
is the same whole horizontal parameter map as the checked discrete
mapping equivalence. A coherent map into the actual row zero can thus
be used in the fixed-edge construction without changing its directed edge.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalRestrictionZeroCalibration

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalRestrictionTranspose (transpose)
open OrdinarySegalCoherentLeftOuterHorn (coherentEdge)
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The exact zero-simplex restriction transpose evaluates to the original
whole horizontal parameter map. -/
theorem transpose_zero (A : SSet.{0}) (W : Space)
    (h : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj A) W) :
    transpose (Δ[0] : SSet.{0}) A W h ≫ (diagramRestrictionSimplexIso W.flip 0).hom =
      (OrdinaryDiscreteMapping.levelEquiv A W ⦋0⦌) (SSet.yonedaEquiv h) := by
  change diagramRestrictionHomEquiv (Δ[0] : SSet.{0}) A W.flip
      (h ≫ (OrdinaryDiscreteMapping.mappingIso A W).hom) ≫
        (diagramRestrictionSimplexIso W.flip 0).hom = _
  rw [diagramRestrictionSimplexIso_hom, diagramRestrictionHomEquiv_π]
  rfl

theorem coherentEdge_transpose_zero (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (OrdinaryDiscreteMapping.levelEquiv (Δ[1] : SSet.{0}) W ⦋0⦌)
        (SSet.yonedaEquiv (coherentEdge W H)) =
      (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H) ≫
        (diagramRestrictionSimplexIso W.flip 0).hom := by
  calc
    _ = transpose (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}) W (coherentEdge W H) ≫
        (diagramRestrictionSimplexIso W.flip 0).hom :=
      (transpose_zero (Δ[1] : SSet.{0}) W (coherentEdge W H)).symm
    _ = _ := by rw [coherentEdge, Equiv.apply_symm_apply]

/-- The actual row-one vertex is the directed edge of the same whole
coherent map evaluated in the original row zero. -/
theorem coherentRowEdge_yoneda (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    SSet.yonedaEquiv (coherentRowEdge W H) =
      SSet.yonedaEquiv
        ((JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H) ≫
          (diagramRestrictionSimplexIso W.flip 0).hom) := by
  change SSet.yonedaEquiv
      ((OrdinaryDiscreteMapping.levelEquiv (Δ[1] : SSet.{0}) W ⦋0⦌)
        (SSet.yonedaEquiv (coherentEdge W H))) = _
  exact congrArg SSet.yonedaEquiv (coherentEdge_transpose_zero W H)

/-- Transporting an actual row-zero coherent map into the restriction
preserves its original directed edge, with no replacement of the time parameter. -/
theorem coherentRowEdge_actual (W : Space) (H : E ⟶ W.flip.obj (op ⦋0⦌)) :
    SSet.yonedaEquiv
        (coherentRowEdge W (H ≫ (diagramRestrictionSimplexIso W.flip 0).inv)) =
      SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H) := by
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    coherentRowEdge_yoneda W (H ≫ (diagramRestrictionSimplexIso W.flip 0).inv)

#print axioms transpose_zero
#print axioms coherentEdge_transpose_zero
#print axioms coherentRowEdge_yoneda
#print axioms coherentRowEdge_actual

end
end DaggerModels.PartII.OrdinarySegalRestrictionZeroCalibration
