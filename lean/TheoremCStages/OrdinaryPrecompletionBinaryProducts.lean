import OrdinarySegalVerticalPrecompletionNaturality
import NativeBisimplicialDiagonal
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Binary products of the corrected vertical precompletion

For each groupoid-simplex parameter and horizontal degree, the strict
mapping-space target functor is a right adjoint. Pointwise preservation,
flipping, and the native diagonal show that the actual corrected
precompletion functor preserves binary products. The resulting comparison
retains the two original projections.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryPrecompletionBinaryProducts

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor post)
open OrdinarySegalVerticalPrecompletionNaturality
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev BiSSet := J ⥤ SSet.{0}

/-- The checked whole-target action on one fixed horizontal cotensor. -/
private def cotensorFunctor (K : SSet.{0}) : Space ⥤ Space where
  obj W := cotensor K W
  map f := post K f
  map_id W := OrdinarySegalHorizontalCotensor.post_id K W
  map_comp f g := OrdinarySegalHorizontalCotensor.post_comp K f g

private instance cotensor_preservesBinaryProducts (K : SSet.{0}) :
    PreservesLimitsOfShape (Discrete WalkingPair) (cotensorFunctor K) := by
  apply preservesLimitsOfShape_of_evaluation
  intro n
  let A := (OrdinarySegalHorizontalCotensor.weight K).obj n.unop
  letI : PreservesLimitsOfSize.{0, 0} (diagramMappingTarget A) :=
    (diagramTensorMappingAdjunction A).rightAdjoint_preservesLimits
  change PreservesLimitsOfShape (Discrete WalkingPair) (diagramMappingTarget A)
  infer_instance

/-- The original groupoid-simplex resolution, functorial in the whole
target ordinary simplicial space. -/
private def resolutionFunctor : Space ⥤ J ⥤ Space where
  obj W := OrdinarySegalPrecompletion.resolution W
  map f := resolutionPost f
  map_id W := resolutionPost_id W
  map_comp f g := resolutionPost_comp f g

private instance resolution_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) resolutionFunctor := by
  apply preservesLimitsOfShape_of_evaluation
  intro q
  change PreservesLimitsOfShape (Discrete WalkingPair)
    (cotensorFunctor (GroupoidSimplex.parameter.obj q.unop))
  infer_instance

/-- The exact corrected precompletion functor preserves binary products.
No fibrancy, Segal, or completeness condition enters this assertion. -/
instance precompletion_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) precompletionFunctor := by
  letI : (flipFunctor J J SSet.{0}).IsEquivalence :=
    (Functor.flipping (C := J) (D := J) (E := SSet.{0})).isEquivalence_functor
  letI : PreservesLimitsOfShape (Discrete WalkingPair)
      (flipFunctor J J SSet.{0}) := inferInstance
  letI : PreservesLimitsOfShape (Discrete WalkingPair)
      ((Functor.whiskeringRight J BiSSet SSet.{0}).obj diagonalFunctor) :=
    inferInstance
  change PreservesLimitsOfShape (Discrete WalkingPair)
    (resolutionFunctor ⋙ flipFunctor J J SSet.{0} ⋙
      (Functor.whiskeringRight J BiSSet SSet.{0}).obj diagonalFunctor)
  infer_instance

/-- Canonical comparison from the precompletion of the actual product to
the product of the two actual precompletions. -/
def productIso (W V : Space) :
    OrdinarySegalVerticalPrecompletion.precompletion (W ⨯ V) ≅
      OrdinarySegalVerticalPrecompletion.precompletion W ⨯
        OrdinarySegalVerticalPrecompletion.precompletion V :=
  PreservesLimitPair.iso precompletionFunctor W V

/-- The first coordinate is exactly the corrected precompletion map of the
original first projection. -/
theorem productIso_fst (W V : Space) :
    (productIso W V).hom ≫ prod.fst = precompletionMap (prod.fst : W ⨯ V ⟶ W) := by
  change prodComparison precompletionFunctor W V ≫ prod.fst = _
  exact prodComparison_fst precompletionFunctor W V

/-- The second coordinate is exactly the corrected precompletion map of the
original second projection. -/
theorem productIso_snd (W V : Space) :
    (productIso W V).hom ≫ prod.snd = precompletionMap (prod.snd : W ⨯ V ⟶ V) := by
  change prodComparison precompletionFunctor W V ≫ prod.snd = _
  exact prodComparison_snd precompletionFunctor W V

#print axioms precompletion_preservesBinaryProducts
#print axioms productIso
#print axioms productIso_fst
#print axioms productIso_snd

end

end DaggerModels.PartII.OrdinaryPrecompletionBinaryProducts
