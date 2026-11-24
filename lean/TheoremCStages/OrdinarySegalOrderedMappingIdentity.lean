import OrdinarySegalOrderedMappingComposition

/-!
# Identity and endpoint normalization for ordered mapping fibers

The induced map of the exact ordered pullback fiber is the identity when
the ambient simplicial-space map is the identity. Equality of whole
composites also gives equality at the two literal zero-simplex endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingIdentity

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (mappingFiber endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingMaps (mappingMap mappingMap_fst mappingMap_snd)

noncomputable section

/-- The original ordered mapping-fiber map of the identity preserves
both pullback projections and is literally the identity. -/
theorem mappingMap_id (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingMap (𝟙 W) x y = 𝟙 (mappingFiber W x y) := by
  change mappingMap (𝟙 W) x y =
    𝟙 (pullback (endpointArrow W) (endpointPoint W x y))
  apply pullback.hom_ext
  · rw [mappingMap_fst]
    change pullback.fst (endpointArrow W) (endpointPoint W x y) ≫ 𝟙 _ =
      𝟙 _ ≫ pullback.fst (endpointArrow W) (endpointPoint W x y)
    simp only [Category.comp_id, Category.id_comp]
  · rw [mappingMap_snd]
    change pullback.snd (endpointArrow W) (endpointPoint W x y) =
      𝟙 _ ≫ pullback.snd (endpointArrow W) (endpointPoint W x y)
    simp only [Category.id_comp]

/-- Whole-map equality after a common source map yields equality at
each actual original zero-simplex, with no endpoint identification assumed. -/
theorem point_comp_eq {W X Y : Space} (s : W ⟶ X) (H c : X ⟶ Y)
    (h : s ≫ H = s ≫ c)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    ((H.app (op ⦋0⦌)).app (op ⦋0⦌))
        (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) x) =
      ((c.app (op ⦋0⦌)).app (op ⦋0⦌))
        (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) x) := by
  have h₀ := congrArg
    (fun α : W ⟶ Y ↦ ((α.app (op ⦋0⦌)).app (op ⦋0⦌)) x) h
  exact h₀

#print axioms mappingMap_id
#print axioms point_comp_eq

end
end DaggerModels.PartII.OrdinarySegalOrderedMappingIdentity
