import OrdinarySegalVerticalPrecompletionDerivedMapping
import OrdinarySegalVerticalPrecompletionUnitAudit

/-!
# The actual corrected unit on chosen derived ordered mapping fibers

The chosen map is induced by the literal degree-one and degree-zero
components of the corrected unit. No target fibrancy is assumed.
Comparison with the original raw JT target remains a separate obligation.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalVerticalPrecompletionDerivedUnit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingMaps (endpointMap endpoint_naturality point_naturality mappingMap)
open OrdinarySegalVerticalPrecompletionFiberComparison (unitVertex)
open ChosenHomotopyFiberComparison (chosenFiber)
open ChosenHomotopyFiberTriangle (inclusion)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W

/-- The original unit square acts on the specified chosen ordered mapping fibers. -/
def unitChosenMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    chosenFiber (endpointArrow W) (endpointPoint W x y) ⟶
      chosenFiber (endpointArrow (P W))
        (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) :=
  ChosenHomotopyFiberFunctor.chosenMap (endpointArrow W) (endpointArrow (P W))
    ((OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌))
    (endpointMap (OrdinarySegalVerticalPrecompletion.unit W))
    (endpoint_naturality (OrdinarySegalVerticalPrecompletion.unit W))
    (endpointPoint W x y) _ (point_naturality (OrdinarySegalVerticalPrecompletion.unit W) x y)

/-- The actual corrected-unit map on the chosen derived fibers is weak. -/
theorem unitChosenMap_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (unitChosenMap W x y) := by
  have : Fibration (endpointArrow W) :=
    OrdinarySegalOrderedMappingFibres.endpointArrow_fibration W
  have : WeakEquivalence (inclusion (endpointArrow W) (endpointPoint W x y)) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  have : WeakEquivalence
      (mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y ≫
        inclusion (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y))) :=
    OrdinarySegalVerticalPrecompletionDerivedMapping.canonicalDerivedMapping_weak W hSegal x y
  have h : inclusion (endpointArrow W) (endpointPoint W x y) ≫ unitChosenMap W x y =
      mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y ≫
        inclusion (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) :=
    ChosenHomotopyFiberFunctor.inclusion_chosenMap _ _ _ _ _ _ _ _
  exact weakEquivalence_of_precomp_of_fac h

/-- At the actual unit-image endpoints, the target strict fiber already
maps weakly to its chosen derived fiber. -/
theorem unitImage_strictInclusion_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (inclusion (endpointArrow (P W))
      (endpointPoint (P W) (unitVertex W x) (unitVertex W y))) := by
  have : WeakEquivalence (mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y) :=
    OrdinarySegalVerticalPrecompletionFiberComparison.mappingMap_unit_weak W hSegal x y
  have : WeakEquivalence
      (mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y ≫
        inclusion (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y))) :=
    OrdinarySegalVerticalPrecompletionDerivedMapping.canonicalDerivedMapping_weak W hSegal x y
  exact weakEquivalence_of_precomp (mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y) _

/-- The same actual chosen-unit comparison at the original ordinary JT input. -/
theorem originalInput_unitChosenMap_weak
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    (x y : ((RawOrdinaryJTQuillenTranspose.input W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (unitChosenMap (RawOrdinaryJTQuillenTranspose.input W) x y) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact unitChosenMap_weak (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) x y

#print axioms unitChosenMap_weak
#print axioms unitImage_strictInclusion_weak
#print axioms originalInput_unitChosenMap_weak

end

end DaggerModels.PartII.OrdinarySegalVerticalPrecompletionDerivedUnit
