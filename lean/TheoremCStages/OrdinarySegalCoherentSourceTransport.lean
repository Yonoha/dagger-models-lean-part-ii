import OrdinarySegalCoherentCompositeFiberNaturality
import OrdinarySegalCoherentFinalFiberNaturality
import OrdinarySegalCoherentFixedSpineIso
import WeakSpanMorphismTransfer

/-!
# Weakness of the original mapping-fiber map is invariant under coherent source change

The two maps from the same whole fixed triangle are actual Kan trivial
fibrations. Their checked target naturality gives a map of weak spans.
Mathlib two-out-of-three then compares the original `mappingMap` at the
two ordered endpoints of the same whole coherent arrow. No weakness of
the middle vertical map or of the desired comparison is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentSourceTransport

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingMaps (mappingMap)
open OrdinarySegalOrderedMappingEndpointTransport (transport)
open OrdinarySegalCoherentFixedTriangleSource (sourceVertex compositeToOriginalFiber)
open OrdinarySegalCoherentFixedSpine (targetVertex finalEdgeFiber)
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)
open OrdinarySegalCoherentFixedTriangleNaturality (fixedTriangleMap)
open OrdinarySegalCoherentVertexNaturality (sourceVertex_post)
open OrdinarySegalCoherentFinalFiberNaturality (targetVertex_post)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- Changing the original source along one whole coherent arrow preserves
weakness of the literal ordered mapping-fiber comparison. -/
theorem mappingMap_weak_iff {W V : Space} [IsFibrant W] [IsFibrant V] (f : W ⟶ V)
    (hW : OrdinaryCSSConditions.segalCondition W)
    (hV : OrdinaryCSSConditions.segalCondition V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f (sourceVertex W H) y) ↔
      WeakEquivalence (mappingMap f (targetVertex W H) y) := by
  let HV := postCoherent f H
  let fy := ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y
  have hL : WeakEquivalence (compositeToOriginalFiber W H y) :=
    ((mem_trivialFibrations_iff _).mp
      (OrdinarySegalCoherentFixedTriangleSource.compositeToOriginalFiber_trivialFibration
        W hW H y)).2
  have hR : WeakEquivalence (finalEdgeFiber W H y) :=
    ((mem_trivialFibrations_iff _).mp
      (OrdinarySegalCoherentFixedSpineIso.finalEdgeFiber_trivialFibration W hW H y)).2
  have hL' : WeakEquivalence
      (compositeToOriginalFiber V HV fy ≫ transport V (sourceVertex_post f H) rfl) := by
    have : WeakEquivalence (compositeToOriginalFiber V HV fy) :=
      ((mem_trivialFibrations_iff _).mp
        (OrdinarySegalCoherentFixedTriangleSource.compositeToOriginalFiber_trivialFibration
          V hV HV fy)).2
    have : WeakEquivalence (transport V (sourceVertex_post f H) (rfl : fy = fy)) := by
      dsimp only [transport]
      infer_instance
    infer_instance
  have hR' : WeakEquivalence
      (finalEdgeFiber V HV fy ≫ transport V (targetVertex_post f H) rfl) := by
    have : WeakEquivalence (finalEdgeFiber V HV fy) :=
      ((mem_trivialFibrations_iff _).mp
        (OrdinarySegalCoherentFixedSpineIso.finalEdgeFiber_trivialFibration V hV HV fy)).2
    have : WeakEquivalence (transport V (targetVertex_post f H) (rfl : fy = fy)) := by
      dsimp only [transport]
      infer_instance
    infer_instance
  rw [weakEquivalence_iff, weakEquivalence_iff]
  exact WeakSpanMorphismTransfer.property_iff (weakEquivalences SSet.{0})
    (compositeToOriginalFiber W H y) (finalEdgeFiber W H y)
    (compositeToOriginalFiber V HV fy ≫ transport V (sourceVertex_post f H) rfl)
    (finalEdgeFiber V HV fy ≫ transport V (targetVertex_post f H) rfl)
    (mappingMap f (sourceVertex W H) y) (mappingMap f (targetVertex W H) y)
    (fixedTriangleMap f H y)
    ((weakEquivalence_iff _).mp hL) ((weakEquivalence_iff _).mp hR)
    ((weakEquivalence_iff _).mp hL') ((weakEquivalence_iff _).mp hR')
    (OrdinarySegalCoherentCompositeFiberNaturality.compositeToOriginalFiber_post f H y)
    (OrdinarySegalCoherentFinalFiberNaturality.finalEdgeFiber_post f H y)

/-- The same statement uses the two actual original groupoid vertices
of a whole coherent map into the original row-zero simplicial set. -/
theorem mappingMap_weak_iff_actual {W V : Space} [IsFibrant W] [IsFibrant V]
    (f : W ⟶ V) (hW : OrdinaryCSSConditions.segalCondition W)
    (hV : OrdinaryCSSConditions.segalCondition V)
    (H : E ⟶ W.flip.obj (op ⦋0⦌))
    (y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f
      (SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H)) y) ↔
    WeakEquivalence (mappingMap f
      (SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H)) y) := by
  let Hr := H ≫ (diagramRestrictionSimplexIso W.flip 0).inv
  have h : ∀ a b : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌),
      a = sourceVertex W Hr → b = targetVertex W Hr →
      (WeakEquivalence (mappingMap f a y) ↔ WeakEquivalence (mappingMap f b y)) := by
    intro a b ha hb
    subst a
    subst b
    exact mappingMap_weak_iff f hW hV Hr y
  exact h _ _ (OrdinarySegalCoherentActualEndpoints.sourceVertex_actual W H).symm
    (OrdinarySegalCoherentFinalFiberNaturality.targetVertex_actual W H).symm

#print axioms mappingMap_weak_iff
#print axioms mappingMap_weak_iff_actual

end
end DaggerModels.PartII.OrdinarySegalCoherentSourceTransport
