import OrdinarySegalConstantWalkingFullyFaithful
import OrdinarySegalOrderedMappingIdentity
import OrdinarySegalCotensorPointEvaluation

/-!
# Evaluation is weak on ordered fibers at constant walking objects

The checked constant walking section is weak on the literal ordered
mapping fibers. Evaluation at either actual groupoid vertex is its strict
retraction, so two-out-of-three makes evaluation weak at precisely those
constant-section objects. No arbitrary-object full-faithfulness claim is
made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalWalkingEvaluationFullyFaithfulAtConstants

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev J : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- At the exact constant images of the original two vertices, evaluation
at any original walking vertex is a Kan weak equivalence of ordered fibers. -/
theorem evaluation_mappingMap_weak (X : Space) [IsFibrant X]
    (hSegal : OrdinaryCSSConditions.segalCondition X)
    (v : (Δ[0] : SSet.{0}) ⟶ J)
    (x y : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (mappingMap (evaluation J X v)
        (((constantSection J X).app (op ⦋0⦌)).app (op ⦋0⦌) x)
        (((constantSection J X).app (op ⦋0⦌)).app (op ⦋0⦌) y)) := by
  let s := constantSection J X
  let e := evaluation J X v
  have hs : WeakEquivalence (mappingMap s x y) :=
    OrdinarySegalConstantWalkingFullyFaithful.mappingMap_weak X hSegal x y
  have hse : s ≫ e = 𝟙 X :=
    OrdinarySegalCotensorPointEvaluation.constantSection_evaluation J X v
  have hcomp : WeakEquivalence (mappingMap (s ≫ e) x y) := by
    rw [hse, OrdinarySegalOrderedMappingIdentity.mappingMap_id]
    infer_instance
  have hfac : WeakEquivalence
      (mappingMap s x y ≫
        mappingMap e
          (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) x)
          (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) y)) := by
    rw [OrdinarySegalOrderedMappingComposition.mappingMap_comp]
    exact hcomp
  haveI : WeakEquivalence (mappingMap s x y) := hs
  haveI : WeakEquivalence
      (mappingMap s x y ≫
        mappingMap e
          (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) x)
          (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) y)) := hfac
  exact weakEquivalence_of_precomp (mappingMap s x y)
    (mappingMap e
      (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) x)
      (((s.app (op ⦋0⦌)).app (op ⦋0⦌)) y))

/-- The same result after explicitly identifying both supplied objects
with the actual constant-section images. -/
theorem evaluation_mappingMap_weak_of_eq (X : Space) [IsFibrant X]
    (hSegal : OrdinaryCSSConditions.segalCondition X)
    (v : (Δ[0] : SSet.{0}) ⟶ J)
    (x y : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (a b : ((cotensor J X).obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (ha : a = (((constantSection J X).app (op ⦋0⦌)).app (op ⦋0⦌)) x)
    (hb : b = (((constantSection J X).app (op ⦋0⦌)).app (op ⦋0⦌)) y) :
    WeakEquivalence (mappingMap (evaluation J X v) a b) := by
  subst a
  subst b
  exact evaluation_mappingMap_weak X hSegal v x y

#print axioms evaluation_mappingMap_weak
#print axioms evaluation_mappingMap_weak_of_eq

end
end DaggerModels.PartII.OrdinarySegalWalkingEvaluationFullyFaithfulAtConstants
