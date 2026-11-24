import OrdinarySegalOrderedMappingMaps
import NativeFibrewiseWeakRecognition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Recognition of the actual ordered endpoint square

The strict endpoint comparison is weak when every original ordered
mapping-fiber map is weak. The proof identifies each vertex base change
with that exact mapping-fiber map through pullback pasting.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalEndpointSquareFiberwiseRecognition

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres
open OrdinarySegalOrderedMappingMaps
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks (mapOver mapOver_fst)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The strict comparison from the source edge row to the actual
pullback of the target endpoint arrow over the source endpoint base. -/
def comparison {W V : Space} (f : W ⟶ V) :
    W.obj (op ⦋1⦌) ⟶
      pullback (endpointArrow V) (endpointMap f) :=
  pullback.lift (f.app (op ⦋1⦌)) (endpointArrow W)
    (endpoint_naturality f).symm

theorem comparison_snd {W V : Space} (f : W ⟶ V) :
    comparison f ≫ pullback.snd (endpointArrow V) (endpointMap f) =
      endpointArrow W := by
  simp only [comparison, pullback.lift_snd]

theorem comparison_fst {W V : Space} (f : W ⟶ V) :
    comparison f ≫ pullback.fst (endpointArrow V) (endpointMap f) =
      f.app (op ⦋1⦌) := by
  simp only [comparison, pullback.lift_fst]

private theorem baseChange_weak_at_pair {W V : Space} (f : W ⟶ V)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (hf : WeakEquivalence (mappingMap f x y)) :
    WeakEquivalence
      (mapOver (endpointArrow W)
        (pullback.snd (endpointArrow V) (endpointMap f))
        (comparison f) (comparison_snd f) (endpointPoint W x y)) := by
  let p := endpointArrow W
  let q := endpointArrow V
  let g := endpointMap f
  let k := pullback.snd q g
  let t := pullback.fst q g
  let b := endpointPoint W x y
  let d := endpointPoint V
    (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x)
    (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y)
  have hb : b ≫ g = d := point_naturality f x y
  let u := mapOver p k (comparison f) (comparison_snd f) b
  have sq : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b) q d := by
    simpa only [k, t, hb] using
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
  let e := sq.isoPullback
  have he : u ≫ e.hom = mappingMap f x y := by
    apply pullback.hom_ext
    · rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc,
        mapOver_fst, Category.assoc]
      rw [show comparison f ≫ t = f.app (op ⦋1⦌) from
        comparison_fst f, mappingMap_fst]
    · rw [Category.assoc, sq.isoPullback_hom_snd, mappingMap_snd]
      dsimp only [u, mapOver]
      exact pullback.lift_snd _ _ _
  have : WeakEquivalence e.hom := inferInstance
  have : WeakEquivalence (u ≫ e.hom) := by rw [he]; exact hf
  exact weakEquivalence_of_postcomp u e.hom

/-- Weakness on every original ordered mapping fiber makes the actual
endpoint square homotopy cartesian in the strict comparison sense. -/
theorem comparison_weak_of_mappingMap_weak {W V : Space}
    [IsFibrant W] [IsFibrant V] (f : W ⟶ V)
    (hf : ∀ x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌),
      WeakEquivalence (mappingMap f x y)) :
    WeakEquivalence (comparison f) := by
  have : Fibration (endpointArrow W) := endpointArrow_fibration W
  have : Fibration (endpointArrow V) := endpointArrow_fibration V
  let p := endpointArrow W
  let k := pullback.snd (endpointArrow V) (endpointMap f)
  have : Fibration k := inferInstance
  apply DaggerNativeFibrewiseWeakRecognition.weak_of_vertex_base_changes
    p k (comparison f) (comparison_snd f)
  intro b
  let x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌) :=
    SSet.yonedaEquiv (b ≫ prod.fst)
  let y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌) :=
    SSet.yonedaEquiv (b ≫ prod.snd)
  have hb : b = endpointPoint W x y := by
    apply prod.hom_ext
    · simp only [endpointPoint_fst, x, Equiv.symm_apply_apply]
    · simp only [endpointPoint_snd, y, Equiv.symm_apply_apply]
  rw [hb]
  exact baseChange_weak_at_pair f x y (hf x y)

#print axioms comparison_snd
#print axioms comparison_fst
#print axioms comparison_weak_of_mappingMap_weak

end
end DaggerModels.PartII.OrdinarySegalEndpointSquareFiberwiseRecognition
