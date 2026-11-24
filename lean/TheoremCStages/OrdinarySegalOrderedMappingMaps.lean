import OrdinarySegalOrderedMappingFibres
import NativeSSetFibrationSquareFibreWeak

/-!
# Actual maps on ordered Segal mapping fibers

A morphism of ordinary simplicial spaces induces a map of the strict ordered
mapping fibers at the original vertices and their actual images. Both the
endpoint square and the specified point square are checked explicitly.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingMaps

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres

noncomputable section

/-- Apply the original degree-zero map to both endpoints in their original order. -/
def endpointMap {W V : Space} (f : W ⟶ V) :
    W.obj (op ⦋0⦌) ⨯ W.obj (op ⦋0⦌) ⟶ V.obj (op ⦋0⦌) ⨯ V.obj (op ⦋0⦌) :=
  prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌))

/-- The whole endpoint arrow commutes with the literal row maps. -/
theorem endpoint_naturality {W V : Space} (f : W ⟶ V) :
    endpointArrow W ≫ endpointMap f = f.app (op ⦋1⦌) ≫ endpointArrow V := by
  apply prod.hom_ext
  · simp only [endpointMap, Category.assoc, prod.map_fst, endpointArrow_fst]
    rw [← Category.assoc, endpointArrow_fst]
    exact f.naturality (SimplexCategory.δ (1 : Fin 2)).op
  · simp only [endpointMap, Category.assoc, prod.map_snd, endpointArrow_snd]
    rw [← Category.assoc, endpointArrow_snd]
    exact f.naturality (SimplexCategory.δ (0 : Fin 2)).op

/-- The original ordered pair maps to exactly the pair of original vertex images. -/
theorem point_naturality {W V : Space} (f : W ⟶ V)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    endpointPoint W x y ≫ endpointMap f =
      endpointPoint V ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
        ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y) := by
  apply prod.hom_ext
  · simp only [endpointMap, Category.assoc, prod.map_fst, endpointPoint_fst]
    rw [← Category.assoc, endpointPoint_fst, SSet.yonedaEquiv_symm_comp]
  · simp only [endpointMap, Category.assoc, prod.map_snd, endpointPoint_snd]
    rw [← Category.assoc, endpointPoint_snd, SSet.yonedaEquiv_symm_comp]

/-- The induced map preserves the exact source pair and its actual images. -/
def mappingMap {W V : Space} (f : W ⟶ V)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶
      mappingFiber V ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
        ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y) :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    (endpointArrow W) (endpointArrow V) (f.app (op ⦋1⦌)) (endpointMap f)
    (endpoint_naturality f) (endpointPoint W x y)
    (endpointPoint V ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y)) (point_naturality f x y)

/-- On the total arrow coordinate this is the literal degree-one component. -/
theorem mappingMap_fst {W V : Space} (f : W ⟶ V)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingMap f x y ≫ pullback.fst _ _ =
      pullback.fst (endpointArrow W) (endpointPoint W x y) ≫ f.app (op ⦋1⦌) :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst _ _ _ _ _ _ _ _

/-- The fixed point object remains the same standard zero-simplex. -/
theorem mappingMap_snd {W V : Space} (f : W ⟶ V)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingMap f x y ≫ pullback.snd _ _ =
      pullback.snd (endpointArrow W) (endpointPoint W x y) :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd _ _ _ _ _ _ _ _

#print axioms endpoint_naturality
#print axioms point_naturality
#print axioms mappingMap_fst
#print axioms mappingMap_snd

end

end DaggerModels.PartII.OrdinarySegalOrderedMappingMaps
