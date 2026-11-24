import OrdinarySegalOrderedMappingIdentity

/-!
# Weakness respects equality of the original whole maps

The target mapping fiber depends on both images of the source vertices.
Eliminating equality of whole maps preserves those dependent targets.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingWeakCongruence

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingMaps (mappingMap)

/-- Equality transports the complete weak-equivalence assertion, including
both dependent target endpoints of the literal mapping-fiber map. -/
theorem weak_congr {W V : Space} {f g : W ⟶ V} (h : f = g)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f x y) ↔ WeakEquivalence (mappingMap g x y) := by
  cases h
  rfl

/-- A whole map equal to the original identity induces weak maps on
the original ordered fibers, retaining the dependent endpoint images. -/
theorem weak_of_eq_id {W : Space} (f : W ⟶ W) (h : f = 𝟙 W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f x y) := by
  apply (weak_congr h x y).mpr
  rw [OrdinarySegalOrderedMappingIdentity.mappingMap_id]
  infer_instance

#print axioms weak_congr
#print axioms weak_of_eq_id

end DaggerModels.PartII.OrdinarySegalOrderedMappingWeakCongruence
