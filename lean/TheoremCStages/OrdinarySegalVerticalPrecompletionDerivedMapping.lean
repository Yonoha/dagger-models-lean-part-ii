import OrdinarySegalEndpointZeroTotalUnit
import OrdinarySegalEndpointPointCalibration
import BisimplicialCommaZeroFiberComparison
import DaggerModelsPartII.ChosenHomotopyFiberFunctor

/-!
# The actual corrected precompletion mapping fiber as a derived fiber

The original ordered mapping map is followed by the canonical inclusion
from the strict fiber to the chosen homotopy fiber. The complete comma
bar comparison identifies this literal composite with a weak map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerSimplicialReplacementChosenFiber (diagonalInclusion)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalVerticalPrecompletionDerivedMapping

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint mappingFiber)
open OrdinarySegalOrderedMappingMaps (mappingMap)
open OrdinarySegalResolutionMappingFibers (endpointResolution pointResolution)
open OrdinarySegalVerticalPrecompletionFiberComparison
open ChosenHomotopyFiberComparison (chosenFiber)
open ChosenHomotopyFiberTriangle (inclusion)
open ChosenHomotopyFiberFunctor (chosenMap inclusion_chosenMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌
private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W
private abbrev f (W : Space) := OrdinarySegalEndpointPointCalibration.endpointArrow W
private abbrev b₀ (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :=
  (pointResolution W x y).app zero
private abbrev σ (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :=
  BisimplicialCommaParameterProjection.zeroSimplexIndex (f W) zero (b₀ W x y)
private abbrev bBar (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :=
  OrdinarySegalEndpointPointCalibration.parameterPoint W x y
private abbrev bDiag (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :=
  SimplicialReplacementChosenHomotopyFiber.pointDiagonalIso.inv ≫
    diagonalFunctor.map (pointResolution W x y)
private abbrev bP (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :=
  endpointPoint (P W) (unitVertex W x) (unitVertex W y)

/-- The reconstructed diagonal point is the actual ordered pair of
images under the corrected precompletion unit. -/
theorem point_to_precompletion (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    bDiag W x y ≫ (baseProductIso W).hom = bP W x y := by
  have h := point_diagonal W x y
  have hzero :
      SimplicialReplacementChosenHomotopyFiber.pointDiagonalIso.inv ≫
          (constantDiagonalIso (Δ[0] : SSet.{0})).hom =
        𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  calc
    _ = SimplicialReplacementChosenHomotopyFiber.pointDiagonalIso.inv ≫
          (diagonalFunctor.map (pointResolution W x y) ≫
            (baseProductIso W).hom) :=
      Category.assoc _ _ _
    _ = SimplicialReplacementChosenHomotopyFiber.pointDiagonalIso.inv ≫
          ((constantDiagonalIso (Δ[0] : SSet.{0})).hom ≫ bP W x y) := by
      rw [h]
    _ = (SimplicialReplacementChosenHomotopyFiber.pointDiagonalIso.inv ≫
          (constantDiagonalIso (Δ[0] : SSet.{0})).hom) ≫ bP W x y :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [hzero, Category.id_comp]

/-- Transport the chosen diagonal fiber through the literal product iso
to the ordered endpoint arrow of the corrected precompletion. -/
def precompletionChosenMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    chosenFiber (diagonalFunctor.map (endpointResolution W)) (bDiag W x y) ⟶
      chosenFiber (endpointArrow (P W)) (bP W x y) :=
  chosenMap (diagonalFunctor.map (endpointResolution W)) (endpointArrow (P W))
    (𝟙 _) (baseProductIso W).hom
    (by simpa only [Category.id_comp] using endpoint_diagonal W)
    (bDiag W x y) (bP W x y) (point_to_precompletion W x y)

theorem precompletionChosenMap_weak (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (precompletionChosenMap W x y) := by
  have : WeakEquivalence (𝟙 ((P W).obj (op ⦋1⦌))) := by infer_instance
  have : WeakEquivalence (baseProductIso W).hom := by infer_instance
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

/-- The strict zero-row comma fiber maps to the same strict fiber of
the complete bar arrow, with its whole parameter simplex retained. -/
def strictBarSource (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶
      pullback (BisimplicialCommaChosenFiberSpan.barArrow (f W)) (bBar W x y) :=
  OrdinarySegalEndpointZeroTotalUnit.zeroFiberComparison W x y ≫
    (BisimplicialCommaZeroFiberComparison.zeroFiberIso
      (f W) zero (b₀ W x y)).hom

private theorem strictBarSource_fst (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    strictBarSource W x y ≫
        pullback.fst (BisimplicialCommaChosenFiberSpan.barArrow (f W))
          (bBar W x y) =
      OrdinarySegalEndpointZeroTotalUnit.zeroFiberComparison W x y ≫
        diagonalInclusion (BisimplicialBaseSimplexFibers.fiberDiagram (f W))
          (σ W x y) := by
  rw [strictBarSource, Category.assoc]
  exact congrArg (OrdinarySegalEndpointZeroTotalUnit.zeroFiberComparison W x y ≫ ·)
    (SimplicialReplacementWeightsChosenFiber.valueFiberIso_fst
      (BisimplicialBaseSimplexFibers.simplexProjection (f W)) (σ W x y))

/-- The pointed reconstruction reaches the strict original diagonal
fiber with exactly the original total and base coordinates. -/
def strictDiagonalMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶
      pullback (diagonalFunctor.map (endpointResolution W)) (bDiag W x y) :=
  strictBarSource W x y ≫
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (BisimplicialCommaChosenFiberSpan.barArrow (f W))
      (diagonalFunctor.map (endpointResolution W))
      (diagonalFunctor.map
        (BisimplicialCommaDiagonalReconstruction.totalReconstruction (f W)))
      (diagonalFunctor.map
        (BisimplicialCommaDiagonalReconstruction.baseReconstruction (f W)))
      (BisimplicialCommaChosenFiberSpan.original_square (f W))
      (bBar W x y) (bDiag W x y)
      (OrdinarySegalEndpointPointCalibration.parameterPoint_reconstruction W x y)

theorem strictDiagonalMap_fst (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    strictDiagonalMap W x y ≫
        pullback.fst (diagonalFunctor.map (endpointResolution W)) (bDiag W x y) =
      pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
        (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌) := by
  rw [strictDiagonalMap, Category.assoc,
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
    ← Category.assoc, strictBarSource_fst]
  exact OrdinarySegalEndpointZeroTotalUnit.zeroFiber_totalReconstruction_unit W x y

/-- The second strict map applies the original diagonal endpoint
identification and retains the identical zero-simplex point. -/
def strictPrecompletionMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ mappingFiber (P W) (unitVertex W x) (unitVertex W y) :=
  strictDiagonalMap W x y ≫
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (diagonalFunctor.map (endpointResolution W)) (endpointArrow (P W))
      (𝟙 _) (baseProductIso W).hom
      (by simpa only [Category.id_comp] using endpoint_diagonal W)
      (bDiag W x y) (bP W x y) (point_to_precompletion W x y)

/-- Both strict pullback coordinates give the literal corrected-unit
ordered mapping map. -/
theorem strictPrecompletionMap_eq_mappingMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    strictPrecompletionMap W x y =
      mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y := by
  rw [← strictUnitFiberComparison_eq_mappingMap W x y]
  apply pullback.hom_ext
  · rw [strictPrecompletionMap, Category.assoc,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
      Category.comp_id, strictDiagonalMap_fst]
    exact (strictUnitFiberComparison_fst W x y).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The exact derived map is the complete bar weak span, evaluated at
the original ordered endpoint pair. -/
def barDerivedMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ chosenFiber (endpointArrow (P W)) (bP W x y) :=
  OrdinarySegalEndpointZeroTotalUnit.zeroFiberComparison W x y ≫
    BisimplicialCommaZeroFiberComparison.zeroFiberToChosen
      (f W) zero (b₀ W x y) ≫
    OrdinarySegalEndpointPointCalibration.originalFiberComparison W x y ≫
    precompletionChosenMap W x y

/-- The chosen-map triangles identify the bar-derived comparison with
the literal strict mapping map followed by its canonical inclusion. -/
theorem barDerivedMap_eq_canonical (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    barDerivedMap W x y =
      mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y ≫
        inclusion (endpointArrow (P W)) (bP W x y) := by
  have h₁ := inclusion_chosenMap
    (BisimplicialCommaChosenFiberSpan.barArrow (f W))
    (diagonalFunctor.map (endpointResolution W))
    (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.totalReconstruction (f W)))
    (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.baseReconstruction (f W)))
    (BisimplicialCommaChosenFiberSpan.original_square (f W))
    (bBar W x y) (bDiag W x y)
    (OrdinarySegalEndpointPointCalibration.parameterPoint_reconstruction W x y)
  have h₂ := inclusion_chosenMap
    (diagonalFunctor.map (endpointResolution W)) (endpointArrow (P W))
    (𝟙 _) (baseProductIso W).hom
    (by simpa only [Category.id_comp] using endpoint_diagonal W)
    (bDiag W x y) (bP W x y) (point_to_precompletion W x y)
  calc
    barDerivedMap W x y =
        strictBarSource W x y ≫
          inclusion (BisimplicialCommaChosenFiberSpan.barArrow (f W))
            (bBar W x y) ≫
          OrdinarySegalEndpointPointCalibration.originalFiberComparison W x y ≫
          precompletionChosenMap W x y := by
      simp only [barDerivedMap, strictBarSource,
        BisimplicialCommaZeroFiberComparison.zeroFiberToChosen, Category.assoc]
      rfl
    _ = strictDiagonalMap W x y ≫
          inclusion (diagonalFunctor.map (endpointResolution W)) (bDiag W x y) ≫
          precompletionChosenMap W x y := by
      simpa only [strictDiagonalMap,
        OrdinarySegalEndpointPointCalibration.originalFiberComparison,
        Category.assoc] using
          congrArg (fun m ↦ strictBarSource W x y ≫ m ≫
            precompletionChosenMap W x y) h₁
    _ = strictPrecompletionMap W x y ≫
          inclusion (endpointArrow (P W)) (bP W x y) := by
      simpa only [strictPrecompletionMap, precompletionChosenMap,
        Category.assoc] using
          congrArg (fun m ↦ strictDiagonalMap W x y ≫ m) h₂
    _ = _ := by rw [strictPrecompletionMap_eq_mappingMap]

/-- The actual corrected precompletion mapping map, followed by the
canonical strict-to-chosen inclusion, is weak at every ordered pair. -/
theorem canonicalDerivedMapping_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y ≫
        inclusion (endpointArrow (P W)) (bP W x y)) := by
  have hFib (r : SimplexCategoryᵒᵖ) :
      Fibration ((endpointResolution W).app r) :=
    OrdinarySegalResolutionRelativeReedy.endpointResolution_row_fibration W r
  have hEqui : BisimplicialEquifibered.Equifibered (f W) :=
    OrdinarySegalResolutionEquifibered.endpointResolution_equifibered W hSegal
  haveI : WeakEquivalence
      (OrdinarySegalEndpointZeroTotalUnit.zeroFiberComparison W x y) :=
    OrdinarySegalEndpointZeroTotalUnit.zeroFiberComparison_weak W hSegal x y
  haveI : WeakEquivalence
      (BisimplicialCommaZeroFiberComparison.zeroFiberToChosen
        (f W) zero (b₀ W x y)) :=
    BisimplicialCommaZeroFiberComparison.zeroFiberToChosen_weak
      (f W) zero (b₀ W x y) hFib hEqui
  haveI : WeakEquivalence
      (OrdinarySegalEndpointPointCalibration.originalFiberComparison W x y) :=
    OrdinarySegalEndpointPointCalibration.originalFiberComparison_weak W x y
  haveI : WeakEquivalence (precompletionChosenMap W x y) :=
    precompletionChosenMap_weak W x y
  rw [← barDerivedMap_eq_canonical]
  unfold barDerivedMap
  infer_instance

#print axioms point_to_precompletion
#print axioms precompletionChosenMap_weak
#print axioms strictPrecompletionMap_eq_mappingMap
#print axioms barDerivedMap_eq_canonical
#print axioms canonicalDerivedMapping_weak

end

end DaggerModels.PartII.OrdinarySegalVerticalPrecompletionDerivedMapping
