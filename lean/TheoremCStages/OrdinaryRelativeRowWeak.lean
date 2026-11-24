import OrdinaryRelativeRows
import OrdinaryRelativeSegal
import OrdinarySegalRowWeakRecognition
import OrdinaryGroupoidSimplexTransitionFullyFaithful

/-!
# All rows of an ordinary fully faithful relative comparison

The original target is pulled back to the original source zero row.
Weakness of all ordered mapping maps then gives weakness in every
horizontal dimension. No ordinary completeness assumption is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryRelativeRowWeak

open OrdinaryCSSLocalization (Space)
open OrdinaryZeroCoskeleton (relativeComparison targetOverZero)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- An ordinary injectively fibrant space has Kan rows. -/
theorem row_fibrant (W : Space) [IsFibrant W] (j : SimplexCategoryᵒᵖ) :
    IsFibrant (W.obj j) :=
  (ProjectiveKanDiagram.model_isFibrant_iff SimplexCategoryᵒᵖ W).mp
    (ProjectiveInjectiveComparison.isFibrant_projective SimplexCategoryᵒᵖ W inferInstance) j

/-- Every row of the relative comparison is weak when every original
ordered mapping map is weak between injectively fibrant Segal spaces. -/
theorem relative_weak {W Z : Space} [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z)
    (hW : OrdinaryCSSConditions.segalCondition W)
    (hZ : OrdinaryCSSConditions.segalCondition Z)
    (hf : ∀ x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌), WeakEquivalence (mappingMap f x y)) :
    WeakEquivalence (relativeComparison f) := by
  have : IsFibrant (W.obj (op ⦋0⦌)) := row_fibrant W _
  have : IsFibrant (targetOverZero f) := OrdinaryZeroCoskeleton.targetOverZero_fibrant f
  have : IsIso ((relativeComparison f).app (op ⦋0⦌)) :=
    OrdinaryRelativeRows.relative_zero_isIso f
  exact OrdinarySegalRowWeakRecognition.weak_of_zero_one (relativeComparison f)
    hW (OrdinaryRelativeSegal.targetOverZero_segal f hZ) inferInstance
    (OrdinaryRelativeRows.relative_one_weak f hf)

/-- Each actual groupoid-simplex restriction is weak after pulling its
target back to the same original source zero row, in every dimension. -/
theorem transition_relative_weak {n m : SimplexCategory} (θ : n ⟶ m)
    (W : Space) [IsFibrant W] (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (relativeComparison
      (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W)) := by
  have : IsFibrant (OrdinarySegalHorizontalCotensor.cotensor
      (GroupoidSimplex.parameter.obj m) W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  have : IsFibrant (OrdinarySegalHorizontalCotensor.cotensor
      (GroupoidSimplex.parameter.obj n) W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  exact relative_weak _
    (OrdinarySegalCotensorSegal.cotensor_segalCondition _ W hSegal)
    (OrdinarySegalCotensorSegal.cotensor_segalCondition _ W hSegal)
    (OrdinaryGroupoidSimplexTransitionFullyFaithful.mappingMap_weak θ W hSegal)

#print axioms relative_weak
#print axioms transition_relative_weak

end

end DaggerModels.PartII.OrdinaryRelativeRowWeak
