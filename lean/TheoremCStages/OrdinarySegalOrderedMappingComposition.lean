import OrdinarySegalOrderedMappingMaps
import OrdinarySegalPrecompletion

/-!
# Composition on the exact ordered mapping fibers

Both the vertex images and the literal fiber maps retain the original
simplicial-space maps. The parameter restriction of a constant section is
the actual constant section for the source parameter.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingComposition

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingMaps
open OrdinarySegalHorizontalCotensor (pre constantMap)
open OrdinarySegalHorizontalCotensorPoint (constantSection)

noncomputable section

/-- Composition preserves the literal original vertices and both fiber projections. -/
theorem mappingMap_comp {W V U : Space} (f : W ⟶ V) (g : V ⟶ U)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingMap f x y ≫ mappingMap g
        ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
        ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y) =
      mappingMap (f ≫ g) x y := by
  apply pullback.hom_ext
  · rw [Category.assoc, mappingMap_fst, ← Category.assoc, mappingMap_fst,
      Category.assoc]
    exact (mappingMap_fst (f ≫ g) x y).symm
  · rw [Category.assoc, mappingMap_snd, mappingMap_snd]
    exact (mappingMap_snd (f ≫ g) x y).symm

/-- Restricting the actual constant section along a parameter map gives
the actual constant section of that same source parameter. -/
theorem constantSection_pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    constantSection L W ≫ pre f W = constantSection K W :=
  OrdinarySegalPrecompletion.constantSection_pre f W

#print axioms mappingMap_comp
#print axioms constantSection_pre

end
end DaggerModels.PartII.OrdinarySegalOrderedMappingComposition
