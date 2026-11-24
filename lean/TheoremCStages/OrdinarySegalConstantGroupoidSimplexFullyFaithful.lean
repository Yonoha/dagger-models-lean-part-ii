import OrdinaryGroupoidSimplexCotensorHomotopyInverse
import OrdinaryGroupoidSimplexCotensorConstantHomotopy
import OrdinarySegalCotensorSegal
import OrdinarySegalWalkingEvaluationFullyFaithfulAtConstants
import OrdinarySegalOrderedMappingWeakCongruence
import OrdinarySegalOrderedMappingRetracts
import SplitSectionArrowRetract

/-!
# Full faithfulness of the original constant groupoid-simplex section

The whole coherent contraction gives a homotopy from the identity of the
actual cotensor to evaluation followed by the original constant section.
On the image of the constant section, both ends of this homotopy lie at
literal constant walking objects. The checked walking evaluation theorem
and the actual arrow retract then give Kan weak equivalences on precisely
the ordered mapping fibers at the original two vertices.

No completeness hypothesis, arbitrary-object Dwyer--Kan assertion, or
replacement of the original parameter map is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalConstantGroupoidSimplexFullyFaithful

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k

/-- The original section into the full groupoid-simplex cotensor is weak
on every literal ordered mapping fiber at original vertices. -/
theorem mappingMap_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (k : SimplexCategory) (j : Fin (k.len + 1))
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (mappingMap (constantSection (E k) W) x y) := by
  let X := cotensor (E k) W
  let s := constantSection (E k) W
  let e := evaluation (E k) W (JTParameterContraction.parameterVertex k j)
  let H := OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W
  let c := constantSection (E ⦋1⦌) X
  let v₀ := JTParameterContraction.parameterVertex ⦋1⦌ 0
  let v₁ := JTParameterContraction.parameterVertex ⦋1⦌ 1
  let e₀ := evaluation (E ⦋1⦌) X v₀
  let e₁ := evaluation (E ⦋1⦌) X v₁
  let sx := ((s.app (op ⦋0⦌)).app (op ⦋0⦌)) x
  let sy := ((s.app (op ⦋0⦌)).app (op ⦋0⦌)) y
  haveI : IsFibrant X :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant (E k) W inferInstance
  have hSegalX : OrdinaryCSSConditions.segalCondition X :=
    OrdinarySegalCotensorSegal.cotensor_segalCondition (E k) W hSegal
  have hHc : s ≫ H = s ≫ c :=
    OrdinaryGroupoidSimplexCotensorConstantHomotopy.constantSection_homotopy k j W
  have hx : ((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sx =
      ((c.app (op ⦋0⦌)).app (op ⦋0⦌)) sx :=
    OrdinarySegalOrderedMappingIdentity.point_comp_eq s H c hHc x
  have hy : ((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sy =
      ((c.app (op ⦋0⦌)).app (op ⦋0⦌)) sy :=
    OrdinarySegalOrderedMappingIdentity.point_comp_eq s H c hHc y
  have he₀ : WeakEquivalence
      (mappingMap e₀
        (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sx)
        (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sy)) :=
    OrdinarySegalWalkingEvaluationFullyFaithfulAtConstants.evaluation_mappingMap_weak_of_eq
      X hSegalX v₀ sx sy _ _ hx hy
  have he₁ : WeakEquivalence
      (mappingMap e₁
        (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sx)
        (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sy)) :=
    OrdinarySegalWalkingEvaluationFullyFaithfulAtConstants.evaluation_mappingMap_weak_of_eq
      X hSegalX v₁ sx sy _ _ hx hy
  have hH₀ : WeakEquivalence (mappingMap (H ≫ e₀) sx sy) :=
    OrdinarySegalOrderedMappingWeakCongruence.weak_of_eq_id
      (H ≫ e₀)
      (OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_zero k j W)
      sx sy
  have hH₀' : WeakEquivalence
      (mappingMap H sx sy ≫
        mappingMap e₀
          (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sx)
          (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sy)) := by
    rw [OrdinarySegalOrderedMappingComposition.mappingMap_comp]
    exact hH₀
  have hH : WeakEquivalence (mappingMap H sx sy) := by
    haveI := he₀
    haveI := hH₀'
    exact weakEquivalence_of_postcomp
      (mappingMap H sx sy)
      (mappingMap e₀
        (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sx)
        (((H.app (op ⦋0⦌)).app (op ⦋0⦌)) sy))
  have hH₁ : WeakEquivalence (mappingMap (H ≫ e₁) sx sy) := by
    rw [← OrdinarySegalOrderedMappingComposition.mappingMap_comp]
    haveI := hH
    haveI := he₁
    infer_instance
  have hes : WeakEquivalence (mappingMap (e ≫ s) sx sy) :=
    (OrdinarySegalOrderedMappingWeakCongruence.weak_congr
      (OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_one k j W)
      sx sy).mp hH₁
  let h : RetractArrow s (e ≫ s) :=
    SplitSectionArrowRetract.sectionRetract s e
      (OrdinaryGroupoidSimplexCotensorHomotopyInverse.section_evaluation k j W)
  have hLarge : weakEquivalences SSet.{0}
      (mappingMap (e ≫ s) sx sy) :=
    (weakEquivalence_iff _).mp hes
  have hSmall : weakEquivalences SSet.{0} (mappingMap s x y) := by
    exact (weakEquivalences SSet.{0}).of_retract
      (OrdinarySegalOrderedMappingRetracts.mappingRetract h x y) hLarge
  exact (weakEquivalence_iff _).mpr hSmall

#print axioms mappingMap_weak

end
end DaggerModels.PartII.OrdinarySegalConstantGroupoidSimplexFullyFaithful
