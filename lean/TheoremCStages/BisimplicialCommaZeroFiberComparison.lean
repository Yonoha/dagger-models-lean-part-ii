import BisimplicialCommaChosenFiberSpan
import SimplicialReplacementWeightsChosenFiber
import SimplicialReplacementNerveChosenFiber
import DaggerModelsPartII.ChosenHomotopyFiberTriangle

/-!
# The exact zero-simplex fiber of the comma parameter bar

At a chosen zero-simplex parameter, the strict fiber of the whole
weight-change map is the original full row fiber. Its canonical map to
the chosen bar fiber commutes with the original pointwise Kan unit and
the chosen fiber of the auxiliary nerve projection.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeSimplicialReplacement (diagonalProjection)
open DaggerNativeSimplicialReplacementWeightsChange (diagonalChange)
open DaggerSimplicialReplacementChosenFiber (chainPoint diagonalInclusion chosenFiberIso)
open DaggerModels.PartII.BisimplicialCommaParameterProjection
open DaggerModels.PartII.BisimplicialCommaChosenFiberSpan
open DaggerModels.PartII.SimplicialReplacementWeightsChosenFiber
open DaggerModels.PartII.SimplicialReplacementNerveChosenFiber
open DaggerModels.PartII.ChosenHomotopyFiberComparison (chosenFiber)
open DaggerModels.PartII.ChosenHomotopyFiberTriangle (inclusion)
open DaggerModels.PartII.ChosenHomotopyFiberFunctor (chosenMap inclusion_chosenMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialCommaZeroFiberComparison

open BisimplicialBaseSimplexFibers (fiberDiagram simplexProjection)
open BisimplicialBaseSimplexKanFibers (kanFiberDiagram)
open BisimplicialCommaDiagonalReconstruction (parameterDiagram)

noncomputable section

variable (f : Arrow BiSSet.{0}) (q : SimplexCategoryᵒᵖ)
variable (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj q)

private abbrev chosenIndex := zeroSimplexIndex f q b
private abbrev chosenPoint := zeroSimplexParameterPoint f q b
private abbrev fiberValues := fiberDiagram f
private abbrev kanValues := kanFiberDiagram f

/-- The strict fiber over the complete zero-simplex parameter is exactly
the original fiber at the same comma object. -/
def zeroFiberIso :
    (fiberValues f).obj (chosenIndex f q b) ≅
      pullback (barArrow f) (chosenPoint f q b) :=
  valueFiberIso (simplexProjection f) (chosenIndex f q b)

/-- Enter the chosen homotopy fiber through its original strict fiber. -/
def zeroFiberToChosen :
    (fiberValues f).obj (chosenIndex f q b) ⟶
      chosenFiber (barArrow f) (chosenPoint f q b) :=
  (zeroFiberIso f q b).hom ≫ inclusion (barArrow f) (chosenPoint f q b)

/-- The auxiliary chosen map has the literal comma point, using the
checked point-projection equality as its square. -/
def calibratedAuxiliaryChosenMap :
    chosenFiber (barArrow f) (chosenPoint f q b) ⟶
      chosenFiber (diagonalProjection (kanValues f)) (chainPoint (chosenIndex f q b)) :=
  chosenMap (barArrow f) (diagonalProjection (kanValues f))
    (diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberValues f)))
    (diagonalProjection (parameterDiagram f)) (auxiliary_square f)
    (chosenPoint f q b) (chainPoint (chosenIndex f q b))
    (zeroSimplexParameterPoint_projection f q b)

/-- The calibrated auxiliary chosen map is weak for any original
bisimplicial arrow. -/
theorem calibratedAuxiliaryChosenMap_weak :
    WeakEquivalence (calibratedAuxiliaryChosenMap f q b) := by
  have : WeakEquivalence
      (diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberValues f))) :=
    SimplicialReplacementPointwiseKan.kanUnit_diagonal_weak (fiberValues f)
  have : WeakEquivalence (diagonalProjection (parameterDiagram f)) :=
    parameterProjection_weak f
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

private theorem nerveFiberIso_fst :
    (chosenFiberIso (kanValues f) (chosenIndex f q b)).hom ≫
        pullback.fst (diagonalProjection (kanValues f))
          (chainPoint (chosenIndex f q b)) =
      diagonalInclusion (kanValues f) (chosenIndex f q b) :=
  (DaggerSimplicialReplacementChosenFiber.diagonalInclusion_isPullback
    (kanValues f) (chosenIndex f q b)).isoPullback_hom_fst

/-- Before the chosen-fiber inclusions, both maps retain the exact
complete constant chain and the same point-object coordinate. -/
theorem zeroFiber_auxiliary_strict_triangle :
    (zeroFiberIso f q b).hom ≫
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
          (barArrow f) (diagonalProjection (kanValues f))
          (diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberValues f)))
          (diagonalProjection (parameterDiagram f)) (auxiliary_square f)
          (chosenPoint f q b) (chainPoint (chosenIndex f q b))
          (zeroSimplexParameterPoint_projection f q b) =
      (SimplicialReplacementPointwiseKan.kanUnit (fiberValues f)).app
          (chosenIndex f q b) ≫
        (chosenFiberIso (kanValues f) (chosenIndex f q b)).hom := by
  have hz : (zeroFiberIso f q b).hom ≫
      pullback.fst (barArrow f) (chosenPoint f q b) =
        diagonalInclusion (fiberValues f) (chosenIndex f q b) :=
    valueFiberIso_fst (simplexProjection f) (chosenIndex f q b)
  apply pullback.hom_ext
  · rw [Category.assoc,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
      ← Category.assoc, hz,
      SimplicialReplacementWeightsChosenFiber.diagonalInclusion_changeWeights,
      Category.assoc, nerveFiberIso_fst]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original strict fiber, followed by the chosen auxiliary map,
is exactly the pointwise Kan unit followed by the nerve chosen fiber. -/
theorem zeroFiber_auxiliary_chosen_triangle :
    zeroFiberToChosen f q b ≫ calibratedAuxiliaryChosenMap f q b =
      (SimplicialReplacementPointwiseKan.kanUnit (fiberValues f)).app
          (chosenIndex f q b) ≫
        nerveValueToChosen (kanValues f) (chosenIndex f q b) := by
  have h := inclusion_chosenMap
    (barArrow f) (diagonalProjection (kanValues f))
    (diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberValues f)))
    (diagonalProjection (parameterDiagram f)) (auxiliary_square f)
    (chosenPoint f q b) (chainPoint (chosenIndex f q b))
    (zeroSimplexParameterPoint_projection f q b)
  calc
    zeroFiberToChosen f q b ≫ calibratedAuxiliaryChosenMap f q b =
        (zeroFiberIso f q b).hom ≫
          (inclusion (barArrow f) (chosenPoint f q b) ≫
            calibratedAuxiliaryChosenMap f q b) := by
              simp only [zeroFiberToChosen, Category.assoc]
    _ = ((zeroFiberIso f q b).hom ≫
          DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
            (barArrow f) (diagonalProjection (kanValues f))
            (diagonalChange
              (SimplicialReplacementPointwiseKan.kanUnit (fiberValues f)))
            (diagonalProjection (parameterDiagram f)) (auxiliary_square f)
            (chosenPoint f q b) (chainPoint (chosenIndex f q b))
            (zeroSimplexParameterPoint_projection f q b)) ≫
          inclusion (diagonalProjection (kanValues f))
            (chainPoint (chosenIndex f q b)) := by
              rw [calibratedAuxiliaryChosenMap, h]
              simp only [Category.assoc]
    _ = _ := by
      rw [zeroFiber_auxiliary_strict_triangle]
      rfl

variable (hFib : ∀ r, Fibration (f.hom.app r))
variable (hEqui : BisimplicialEquifibered.Equifibered f)

include hFib hEqui in
/-- With original row fibrations and equifibered transitions, the
canonical map from the actual zero fiber to the chosen bar fiber is weak. -/
theorem zeroFiberToChosen_weak : WeakEquivalence (zeroFiberToChosen f q b) := by
  have hK : ∀ ⦃s t : BisimplicialBaseSimplexFibers.Index f⦄ (a : s ⟶ t),
      WeakEquivalence ((kanValues f).map a) := by
    intro s t a
    exact BisimplicialBaseSimplexKanFibers.kanFiberDiagram_map_weak f hFib hEqui a
  haveI : WeakEquivalence
      ((SimplicialReplacementPointwiseKan.kanUnit (fiberValues f)).app
        (chosenIndex f q b)) :=
    SimplicialReplacementPointwiseKan.kanUnit_value_weak
      (fiberValues f) (chosenIndex f q b)
  haveI : WeakEquivalence (nerveValueToChosen (kanValues f) (chosenIndex f q b)) :=
    nerveValueToChosen_weak (kanValues f) hK (chosenIndex f q b)
  haveI : WeakEquivalence (calibratedAuxiliaryChosenMap f q b) :=
    calibratedAuxiliaryChosenMap_weak f q b
  haveI : WeakEquivalence
      (zeroFiberToChosen f q b ≫ calibratedAuxiliaryChosenMap f q b) := by
    rw [zeroFiber_auxiliary_chosen_triangle]
    infer_instance
  exact weakEquivalence_of_postcomp_of_fac
    (zeroFiber_auxiliary_chosen_triangle f q b)

#print axioms zeroFiberIso
#print axioms zeroFiberToChosen
#print axioms calibratedAuxiliaryChosenMap_weak
#print axioms zeroFiber_auxiliary_strict_triangle
#print axioms zeroFiber_auxiliary_chosen_triangle
#print axioms zeroFiberToChosen_weak

end

end DaggerModels.PartII.BisimplicialCommaZeroFiberComparison
