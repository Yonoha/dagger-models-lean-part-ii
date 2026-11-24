import OrdinaryWalkingCoherentObject

/-!
# The actual constant cotensor object as a whole parameter map

The row-zero unitor and the original representable mapping isomorphism
identify the actual constant-section object with the map constant at the
same original vertex. All horizontal and vertical degrees are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCotensorConstantObject

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalWalkingEvaluation (simplexMappingIso)
open OrdinaryWalkingCoherentObject (objectMap)

noncomputable section

private theorem level_pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space)
    (q : SimplexCategoryᵒᵖ) (z : (diagramMappingSpace (discrete.obj L) W).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv K W q.unop)
        ((diagramMappingPrecomp (discrete.map f) W).app q z) =
      f ≫ (OrdinaryDiscreteMapping.levelEquiv L W q.unop) z := by
  have h := congrFun
    (NatTrans.congr_app (OrdinaryDiscreteMapping.mappingIso_natural f W) q) z
  simpa only [OrdinaryDiscreteMapping.mappingIso, OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre, Equiv.coe_fn_mk] using h

/-- The full parameter map of an actual constant-section object is
constant at that same original vertex, with no fibrancy hypothesis. -/
theorem objectMap_constant (K : SSet.{0}) (W : Space)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    objectMap K W (((constantSection K W).app (op ⦋0⦌)).app (op ⦋0⦌) x) =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        (SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)).symm x := by
  have hc := congrFun (NatTrans.congr_app
    (OrdinarySegalCotensorZeroIso.constantSection_mappingIso K W) (op ⦋0⦌)) x
  change (OrdinaryDiscreteMapping.levelEquiv K W ⦋0⦌)
    ((OrdinarySegalCotensorZeroIso.mappingIso K W).hom.app (op ⦋0⦌)
      (((constantSection K W).app (op ⦋0⦌)).app (op ⦋0⦌) x)) = _
  change (OrdinarySegalCotensorZeroIso.mappingIso K W).hom.app (op ⦋0⦌)
      (((constantSection K W).app (op ⦋0⦌)).app (op ⦋0⦌) x) =
    (diagramMappingPrecomp (discrete.map (SSet.stdSimplex.isTerminalObj₀.from K)) W).app
      (op ⦋0⦌) ((simplexMappingIso W 0).inv.app (op ⦋0⦌) x) at hc
  rw [hc, level_pre]
  congr 1
  apply SSet.yonedaEquiv.injective
  change (simplexMappingIso W 0).hom.app (op ⦋0⦌)
      ((simplexMappingIso W 0).inv.app (op ⦋0⦌) x) =
    SSet.yonedaEquiv
      ((SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)).symm x)
  rw [Equiv.apply_symm_apply]
  exact congrFun (NatTrans.congr_app (simplexMappingIso W 0).inv_hom_id (op ⦋0⦌)) x

#print axioms objectMap_constant

end
end DaggerModels.PartII.OrdinarySegalCotensorConstantObject
