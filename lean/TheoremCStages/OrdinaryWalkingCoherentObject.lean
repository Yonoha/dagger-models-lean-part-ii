import OrdinaryWalkingCoherentCotensorArrow
import OrdinarySegalCotensorZeroIso

/-!
# Whole parameter maps from the literal objects of the walking cotensor

The checked row-zero unitor comparison and discrete mapping isomorphism
extract the entire horizontal parameter map of every actual cotensor
object. Currying the coherent walking contraction then gives an arrow
with that same source object.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingCoherentObject

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinaryWalkingCoherentCotensorArrow (arrow)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The original cotensor object is exactly a horizontal parameter map. -/
def objectIso (K : SSet.{0}) (W : Space) :
    (cotensor K W).obj (op ⦋0⦌) ≅
      DaggerNativeBisimplicialHorizontalMapping.horizontalMapping K W :=
  OrdinarySegalCotensorZeroIso.mappingIso K W ≪≫
    OrdinaryDiscreteMapping.mappingIso K W

/-- A literal zero-simplex supplies its complete parameter map. -/
def objectMap (K : SSet.{0}) (W : Space)
    (z : ((cotensor K W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    K ⟶ W.flip.obj (op ⦋0⦌) :=
  (objectIso K W).hom.app (op ⦋0⦌) z

/-- The coherent walking arrow associated to a literal cotensor object. -/
def objectArrow (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (j : Fin 2) : E ⟶ (cotensor E W).flip.obj (op ⦋0⦌) :=
  arrow W (op ⦋0⦌) (objectMap E W z) j

#print axioms objectIso
#print axioms objectMap
#print axioms objectArrow

end
end DaggerModels.PartII.OrdinaryWalkingCoherentObject
