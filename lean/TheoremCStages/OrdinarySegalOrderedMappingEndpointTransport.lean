import OrdinarySegalOrderedMappingMaps

/-!
# Equality transport for the literal ordered Segal mapping fibers

Both endpoint equalities transport the entire strict pullback fiber,
including its specified ordered boundary point. Naturality uses the
actual `mappingMap` induced by a whole morphism of ordinary simplicial
spaces. The older simplicial-category Hom transport has a different
source type and is not substituted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingEndpointTransport

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (mappingFiber)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

/-- Equality of both original ordered vertices transports the exact
strict pullback fiber, with its unchanged endpoint arrow. -/
def transport (W : Space)
    {x x' y y' : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)}
    (hx : x = x') (hy : y = y') :
    mappingFiber W x y ⟶ mappingFiber W x' y' :=
  eqToHom (by cases hx; cases hy; rfl)

@[simp] theorem transport_refl (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    transport W (rfl : x = x) (rfl : y = y) = 𝟙 _ := rfl

theorem transport_comp (W : Space)
    {x x' x'' y y' y'' : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)}
    (hx : x = x') (hx' : x' = x'')
    (hy : y = y') (hy' : y' = y'') :
    transport W hx hy ≫ transport W hx' hy' =
      transport W (hx.trans hx') (hy.trans hy') := by
  cases hx
  cases hx'
  cases hy
  cases hy'
  simp

/-- The same endpoint equalities commute with the actual induced
mapping-fiber map of a whole simplicial-space morphism. -/
theorem transport_map {W V : Space} (f : W ⟶ V)
    {x x' y y' : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)}
    (hx : x = x') (hy : y = y') :
    transport W hx hy ≫ mappingMap f x' y' =
      mappingMap f x y ≫ transport V
        (congrArg (fun z ↦ ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) z) hx)
        (congrArg (fun z ↦ ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) z) hy) := by
  cases hx
  cases hy
  simp

/-- Equality of whole simplicial-space maps includes the necessary
transport between their two actual target endpoint pairs. -/
theorem map_of_eq {W V : Space} {f g : W ⟶ V}
    (h : f = g) (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingMap f x y ≫ transport V
        (congrArg
          (fun k : W ⟶ V ↦ ((k.app (op ⦋0⦌)).app (op ⦋0⦌)) x) h)
        (congrArg
          (fun k : W ⟶ V ↦ ((k.app (op ⦋0⦌)).app (op ⦋0⦌)) y) h) =
      mappingMap g x y := by
  cases h
  simp

#print axioms transport_refl
#print axioms transport_comp
#print axioms transport_map
#print axioms map_of_eq

end
end DaggerModels.PartII.OrdinarySegalOrderedMappingEndpointTransport
