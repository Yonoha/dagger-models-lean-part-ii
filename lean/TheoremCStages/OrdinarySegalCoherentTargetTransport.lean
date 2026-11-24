import OrdinarySegalCoherentRightFiberNaturality
import OrdinarySegalCoherentRightFixedSpineIso
import WeakSpanMorphismTransfer

/-!
# Weakness of the original mapping-fiber map is invariant under coherent target change

The two maps from the same whole fixed triangle are actual Kan trivial
fibrations. Their checked naturality gives a map of weak spans.
Mathlib two-out-of-three then compares the original `mappingMap` at the
two ordered endpoints of the same whole coherent arrow. No weakness of
the middle vertical map or of the desired comparison is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentTargetTransport

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingMaps (mappingMap)
open OrdinarySegalOrderedMappingEndpointTransport (transport)
open OrdinarySegalCoherentRightFixedTriangleTarget (targetVertex compositeToOriginalFiber)
open OrdinarySegalCoherentRightFixedSpine (sourceVertex firstEdgeFiber)
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)
open OrdinarySegalCoherentRightFixedTriangleNaturality (fixedTriangleMap)
open OrdinarySegalCoherentRightFiberNaturality (sourceVertex_post)
open OrdinarySegalCoherentRightFiberNaturality (targetVertex_post)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- Changing the original target along one whole coherent arrow preserves
weakness of the literal ordered mapping-fiber comparison. -/
theorem mappingMap_weak_iff_reverse {W V : Space} [IsFibrant W] [IsFibrant V] (f : W ⟶ V)
    (hW : OrdinaryCSSConditions.segalCondition W)
    (hV : OrdinaryCSSConditions.segalCondition V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f x (targetVertex W H)) ↔
      WeakEquivalence (mappingMap f x (sourceVertex W H)) := by
  let HV := postCoherent f H
  let fy := ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x
  have hL : WeakEquivalence (compositeToOriginalFiber W H x) :=
    ((mem_trivialFibrations_iff _).mp
      (OrdinarySegalCoherentRightFixedTriangleTarget.compositeToOriginalFiber_trivialFibration
        W hW H x)).2
  have hR : WeakEquivalence (firstEdgeFiber W H x) :=
    ((mem_trivialFibrations_iff _).mp
      (OrdinarySegalCoherentRightFixedSpineIso.firstEdgeFiber_trivialFibration W hW H x)).2
  have hL' : WeakEquivalence
      (compositeToOriginalFiber V HV fy ≫ transport V rfl (targetVertex_post f H)) := by
    have : WeakEquivalence (compositeToOriginalFiber V HV fy) :=
      ((mem_trivialFibrations_iff _).mp
        (OrdinarySegalCoherentRightFixedTriangleTarget.compositeToOriginalFiber_trivialFibration
          V hV HV fy)).2
    have : WeakEquivalence (transport V (rfl : fy = fy) (targetVertex_post f H)) := by
      dsimp only [transport]
      infer_instance
    infer_instance
  have hR' : WeakEquivalence
      (firstEdgeFiber V HV fy ≫ transport V rfl (sourceVertex_post f H)) := by
    have : WeakEquivalence (firstEdgeFiber V HV fy) :=
      ((mem_trivialFibrations_iff _).mp
        (OrdinarySegalCoherentRightFixedSpineIso.firstEdgeFiber_trivialFibration V hV HV fy)).2
    have : WeakEquivalence (transport V (rfl : fy = fy) (sourceVertex_post f H)) := by
      dsimp only [transport]
      infer_instance
    infer_instance
  rw [weakEquivalence_iff, weakEquivalence_iff]
  exact WeakSpanMorphismTransfer.property_iff (weakEquivalences SSet.{0})
    (compositeToOriginalFiber W H x) (firstEdgeFiber W H x)
    (compositeToOriginalFiber V HV fy ≫ transport V rfl (targetVertex_post f H))
    (firstEdgeFiber V HV fy ≫ transport V rfl (sourceVertex_post f H))
    (mappingMap f x (targetVertex W H)) (mappingMap f x (sourceVertex W H))
    (fixedTriangleMap f H x)
    ((weakEquivalence_iff _).mp hL) ((weakEquivalence_iff _).mp hR)
    ((weakEquivalence_iff _).mp hL') ((weakEquivalence_iff _).mp hR')
    (OrdinarySegalCoherentRightFiberNaturality.compositeToOriginalFiber_post f H x)
    (OrdinarySegalCoherentRightFiberNaturality.firstEdgeFiber_post f H x)

/-- The original target can move along the coherent edge in either direction
without changing weakness of the ordered mapping-fiber map. -/
theorem mappingMap_weak_iff {W V : Space} [IsFibrant W] [IsFibrant V] (f : W ⟶ V)
    (hW : OrdinaryCSSConditions.segalCondition W)
    (hV : OrdinaryCSSConditions.segalCondition V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f x (sourceVertex W H)) ↔
      WeakEquivalence (mappingMap f x (targetVertex W H)) :=
  (mappingMap_weak_iff_reverse f hW hV H x).symm

/-- The same statement uses the two actual original groupoid vertices
of a whole coherent map into the original row-zero simplicial set. -/
theorem mappingMap_weak_iff_actual {W V : Space} [IsFibrant W] [IsFibrant V]
    (f : W ⟶ V) (hW : OrdinaryCSSConditions.segalCondition W)
    (hV : OrdinaryCSSConditions.segalCondition V)
    (H : E ⟶ W.flip.obj (op ⦋0⦌))
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f x
      (SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H))) ↔
    WeakEquivalence (mappingMap f x
      (SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H))) := by
  let Hr := H ≫ (diagramRestrictionSimplexIso W.flip 0).inv
  have h : ∀ a b : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌),
      a = sourceVertex W Hr → b = targetVertex W Hr →
      (WeakEquivalence (mappingMap f x a) ↔ WeakEquivalence (mappingMap f x b)) := by
    intro a b ha hb
    subst a
    subst b
    exact mappingMap_weak_iff f hW hV Hr x
  exact h _ _ (OrdinarySegalCoherentRightFiberNaturality.sourceVertex_actual W H).symm
    (OrdinarySegalCoherentRightFiberNaturality.targetVertex_actual W H).symm

#print axioms mappingMap_weak_iff
#print axioms mappingMap_weak_iff_actual

end
end DaggerModels.PartII.OrdinarySegalCoherentTargetTransport
