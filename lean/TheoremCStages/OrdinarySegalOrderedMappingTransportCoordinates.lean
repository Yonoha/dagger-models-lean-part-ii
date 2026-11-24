import OrdinarySegalOrderedMappingEndpointTransport

/-!
# Equality transport preserves both original ordered-fiber projections

Endpoint equality changes only the specified point of the pullback. The
total edge coordinate and the fixed zero-simplex coordinate are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingTransportCoordinates

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingEndpointTransport (transport transport_refl)

theorem transport_fst (W : Space)
    {x x' y y' : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)} (hx : x = x') (hy : y = y') :
    transport W hx hy ≫ pullback.fst (endpointArrow W) (endpointPoint W x' y') =
      pullback.fst (endpointArrow W) (endpointPoint W x y) := by
  cases hx
  cases hy
  rw [transport_refl, Category.id_comp]

theorem transport_snd (W : Space)
    {x x' y y' : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)} (hx : x = x') (hy : y = y') :
    transport W hx hy ≫ pullback.snd (endpointArrow W) (endpointPoint W x' y') =
      pullback.snd (endpointArrow W) (endpointPoint W x y) := by
  cases hx
  cases hy
  rw [transport_refl, Category.id_comp]

#print axioms transport_fst
#print axioms transport_snd

end DaggerModels.PartII.OrdinarySegalOrderedMappingTransportCoordinates
