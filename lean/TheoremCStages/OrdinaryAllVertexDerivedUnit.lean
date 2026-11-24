import OrdinaryAllVertexPointReconstruction
import BisimplicialCommaZeroFiberComparison
import DaggerModelsPartII.ChosenHomotopyFiberFunctor

/-!
# The actual corrected unit on every chosen full-tuple fiber

The full comma weak span is evaluated at the unchanged original finite tuple.
Its total coordinate is the actual corrected unit in horizontal degree n.
The canonical strict-to-chosen composite is weak without assuming that the
precompletion is fibrant, Segal after replacement, or complete.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerSimplicialReplacementChosenFiber (diagonalInclusion)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryAllVertexDerivedUnit

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap)
open OrdinarySegalAllVertexDescent (vertexArrow)
open OrdinarySegalAllVertexDiagonal (vertexBaseDiagonalIso)
open OrdinaryAllVertexPointReconstruction
open ChosenHomotopyFiberComparison (chosenFiber)
open ChosenHomotopyFiberTriangle (inclusion)
open ChosenHomotopyFiberFunctor (chosenMap inclusion_chosenMap)

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌
private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W

/-- The original full tuple mapped by the actual corrected unit. -/
def unitPoint (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :=
  b ≫ diagramMappingPostcomp (discrete.obj (vertices n))
    (OrdinarySegalVerticalPrecompletion.unit W)

/-- The original diagonal vertex arrow, expressed over the precompletion base. -/
theorem diagonalArrow_to_precompletion (W : Space) (n : ℕ) :
    diagonalFunctor.map (vertexArrow W n).hom ≫ (vertexBaseDiagonalIso W n).inv =
      vertexMap (P W) n := by
  change diagonalFunctor.map (OrdinarySegalAllVertexResolution.vertexResolution W n) ≫
    (vertexBaseDiagonalIso W n).inv = vertexMap (P W) n
  rw [← OrdinarySegalAllVertexDiagonalCalibration.vertexMap_diagonal W n]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The same original full tuple point under the inverse base identification. -/
theorem diagonalPoint_to_precompletion (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    diagonalPoint W n b ≫ (vertexBaseDiagonalIso W n).inv = unitPoint W n b := by
  rw [← diagonalPoint_unit W n b]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, unitPoint]

/-- Transport of the chosen fiber uses the actual whole vertex base isomorphism. -/
def precompletionChosenMap (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    chosenFiber (diagonalFunctor.map (vertexArrow W n).hom) (diagonalPoint W n b) ⟶
      chosenFiber (vertexMap (P W) n) (unitPoint W n b) :=
  chosenMap _ _ (𝟙 _) (vertexBaseDiagonalIso W n).inv
    (by simpa only [Category.id_comp] using diagonalArrow_to_precompletion W n)
    _ _ (diagonalPoint_to_precompletion W n b)

theorem precompletionChosenMap_weak (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence (precompletionChosenMap W n b) := by
  have : WeakEquivalence (vertexBaseDiagonalIso W n).inv := inferInstance
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

/-- The chosen original comma reconstruction at the same full tuple. -/
def originalFiberComparison (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    chosenFiber (BisimplicialCommaChosenFiberSpan.barArrow (vertexArrow W n))
        (parameterPoint W n b) ⟶
      chosenFiber (diagonalFunctor.map (vertexArrow W n).hom) (diagonalPoint W n b) :=
  chosenMap _ _
    (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.totalReconstruction (vertexArrow W n)))
    (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.baseReconstruction (vertexArrow W n)))
    (BisimplicialCommaChosenFiberSpan.original_square (vertexArrow W n))
    _ _ (parameterPoint_reconstruction W n b)

theorem originalFiberComparison_weak (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence (originalFiberComparison W n b) := by
  have : WeakEquivalence (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.totalReconstruction (vertexArrow W n))) :=
    BisimplicialCommaDiagonalReconstruction.totalReconstruction_diagonal_weak _
  have : WeakEquivalence (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.baseReconstruction (vertexArrow W n))) :=
    BisimplicialCommaDiagonalReconstruction.baseReconstruction_diagonal_weak _
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

private abbrev index (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :=
  BisimplicialCommaParameterProjection.zeroSimplexIndex
    (vertexArrow W n) zero (zeroBoundary W n b)

/-- The whole source fiber enters the original strict bar fiber. -/
def strictBarSource (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :=
  zeroFiberComparison W n b ≫
    (BisimplicialCommaZeroFiberComparison.zeroFiberIso
      (vertexArrow W n) zero (zeroBoundary W n b)).hom

private theorem strictBarSource_fst (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    strictBarSource W n b ≫
        pullback.fst (BisimplicialCommaChosenFiberSpan.barArrow (vertexArrow W n))
          (parameterPoint W n b) =
      zeroFiberComparison W n b ≫
        diagonalInclusion (BisimplicialBaseSimplexFibers.fiberDiagram (vertexArrow W n))
          (index W n b) := by
  rw [strictBarSource, Category.assoc]
  exact congrArg (zeroFiberComparison W n b ≫ ·)
    (SimplicialReplacementWeightsChosenFiber.valueFiberIso_fst
      (BisimplicialBaseSimplexFibers.simplexProjection (vertexArrow W n)) (index W n b))

/-- The reconstructed strict diagonal fiber retains both original coordinates. -/
def strictDiagonalMap (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :=
  strictBarSource W n b ≫
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (BisimplicialCommaChosenFiberSpan.barArrow (vertexArrow W n))
      (diagonalFunctor.map (vertexArrow W n).hom)
      (diagonalFunctor.map
        (BisimplicialCommaDiagonalReconstruction.totalReconstruction (vertexArrow W n)))
      (diagonalFunctor.map
        (BisimplicialCommaDiagonalReconstruction.baseReconstruction (vertexArrow W n)))
      (BisimplicialCommaChosenFiberSpan.original_square (vertexArrow W n))
      (parameterPoint W n b) (diagonalPoint W n b) (parameterPoint_reconstruction W n b)

theorem strictDiagonalMap_fst (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    strictDiagonalMap W n b ≫
        pullback.fst (diagonalFunctor.map (vertexArrow W n).hom) (diagonalPoint W n b) =
      pullback.fst (vertexMap W n) b ≫
        (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋n⦌) := by
  rw [strictDiagonalMap, Category.assoc,
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
    ← Category.assoc, strictBarSource_fst]
  exact zeroFiber_totalReconstruction_unit W n b

/-- Transport to the literal full-tuple strict fiber of the precompletion. -/
def strictPrecompletionMap (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :=
  strictDiagonalMap W n b ≫
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (diagonalFunctor.map (vertexArrow W n).hom) (vertexMap (P W) n)
      (𝟙 _) (vertexBaseDiagonalIso W n).inv
      (by simpa only [Category.id_comp] using diagonalArrow_to_precompletion W n)
      (diagonalPoint W n b) (unitPoint W n b) (diagonalPoint_to_precompletion W n b)

/-- The complete reconstruction is the actual original unit's full-tuple fiber map. -/
theorem strictPrecompletionMap_eq_tupleMap (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    strictPrecompletionMap W n b =
      OrdinaryAllVertexStrictFibreMap.tupleMap
        (OrdinarySegalVerticalPrecompletion.unit W) n b := by
  apply pullback.hom_ext
  · rw [strictPrecompletionMap, Category.assoc,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
      Category.comp_id, strictDiagonalMap_fst]
    exact (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst _ _ _ _ _ _ _ _).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The weak chosen comparison obtained through the full original comma span. -/
def barDerivedMap (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :=
  zeroFiberComparison W n b ≫
    BisimplicialCommaZeroFiberComparison.zeroFiberToChosen
      (vertexArrow W n) zero (zeroBoundary W n b) ≫
    originalFiberComparison W n b ≫ precompletionChosenMap W n b

/-- The weak span is exactly the canonical strict-unit-to-chosen-fiber composite. -/
theorem barDerivedMap_eq_canonical (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    barDerivedMap W n b =
      OrdinaryAllVertexStrictFibreMap.tupleMap
          (OrdinarySegalVerticalPrecompletion.unit W) n b ≫
        inclusion (vertexMap (P W) n) (unitPoint W n b) := by
  have h₁ := inclusion_chosenMap
    (BisimplicialCommaChosenFiberSpan.barArrow (vertexArrow W n))
    (diagonalFunctor.map (vertexArrow W n).hom)
    (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.totalReconstruction (vertexArrow W n)))
    (diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.baseReconstruction (vertexArrow W n)))
    (BisimplicialCommaChosenFiberSpan.original_square (vertexArrow W n))
    (parameterPoint W n b) (diagonalPoint W n b) (parameterPoint_reconstruction W n b)
  have h₂ := inclusion_chosenMap
    (diagonalFunctor.map (vertexArrow W n).hom) (vertexMap (P W) n)
    (𝟙 _) (vertexBaseDiagonalIso W n).inv
    (by simpa only [Category.id_comp] using diagonalArrow_to_precompletion W n)
    (diagonalPoint W n b) (unitPoint W n b) (diagonalPoint_to_precompletion W n b)
  calc
    barDerivedMap W n b = strictBarSource W n b ≫
        inclusion (BisimplicialCommaChosenFiberSpan.barArrow (vertexArrow W n))
          (parameterPoint W n b) ≫
        originalFiberComparison W n b ≫ precompletionChosenMap W n b := by
      simp only [barDerivedMap, strictBarSource,
        BisimplicialCommaZeroFiberComparison.zeroFiberToChosen, Category.assoc]
      rfl
    _ = strictDiagonalMap W n b ≫
        inclusion (diagonalFunctor.map (vertexArrow W n).hom) (diagonalPoint W n b) ≫
        precompletionChosenMap W n b := by
      simpa only [strictDiagonalMap, originalFiberComparison, Category.assoc] using
        congrArg (fun m ↦ strictBarSource W n b ≫ m ≫ precompletionChosenMap W n b) h₁
    _ = strictPrecompletionMap W n b ≫
        inclusion (vertexMap (P W) n) (unitPoint W n b) := by
      simpa only [strictPrecompletionMap, precompletionChosenMap, Category.assoc] using
        congrArg (fun m ↦ strictDiagonalMap W n b ≫ m) h₂
    _ = _ := by rw [strictPrecompletionMap_eq_tupleMap]

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The actual corrected unit is weak on every chosen full ordered-tuple fiber. -/
theorem canonicalDerivedTupleMap_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence
      (OrdinaryAllVertexStrictFibreMap.tupleMap
          (OrdinarySegalVerticalPrecompletion.unit W) n b ≫
        inclusion (vertexMap (P W) n) (unitPoint W n b)) := by
  have : WeakEquivalence (zeroFiberComparison W n b) :=
    zeroFiberComparison_weak W hSegal n b
  have : WeakEquivalence (BisimplicialCommaZeroFiberComparison.zeroFiberToChosen
      (vertexArrow W n) zero (zeroBoundary W n b)) :=
    OrdinarySegalAllVertexDescent.zeroFiberToChosen_weak W hSegal n zero (zeroBoundary W n b)
  have : WeakEquivalence (originalFiberComparison W n b) :=
    originalFiberComparison_weak W n b
  have : WeakEquivalence (precompletionChosenMap W n b) :=
    precompletionChosenMap_weak W n b
  rw [← barDerivedMap_eq_canonical]
  unfold barDerivedMap
  infer_instance

#print axioms diagonalArrow_to_precompletion
#print axioms precompletionChosenMap_weak
#print axioms originalFiberComparison_weak
#print axioms strictPrecompletionMap_eq_tupleMap
#print axioms barDerivedMap_eq_canonical
#print axioms canonicalDerivedTupleMap_weak

end

end DaggerModels.PartII.OrdinaryAllVertexDerivedUnit
