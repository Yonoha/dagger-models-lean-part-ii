import DaggerModelsPartII.JTGraphParameterRelative
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv
import DaggerModelsPartII.JTGraphLiftTransport

/-!
# The exact parameter lift space of an actual reduced-cylinder map
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphParameterLiftSpace

open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable {X : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
variable (f : X ⟶ T.toSSet) (g : X ⟶ (value T).obj k)

/-- The map on simplicial mapping objects given by the original cylinder,
with the full horizontal coordinate fixed. -/
def graphMap : (ihom X).obj (J.obj k) ⟶ (ihom X).obj ((value T).obj k) :=
  curry (lift (fst X ((ihom X).obj (J.obj k)) ≫ f) (uncurry (𝟙 _)) ≫
    (cylinder T).app k)

private theorem uncurry_graphMap {Y : SSet.{0}}
    (p : Y ⟶ (ihom X).obj (J.obj k)) :
    uncurry (p ≫ graphMap T k f) =
      lift (fst X Y ≫ f) (uncurry p) ≫ (cylinder T).app k := by
  rw [uncurry_natural_left, graphMap, uncurry_curry, ← Category.assoc,
    CartesianMonoidalCategory.comp_lift]
  have h₀ : (X ◁ p) ≫ fst X ((ihom X).obj (J.obj k)) ≫ f = fst X Y ≫ f :=
    by rw [whiskerLeft_fst_assoc]
  have h₁ : (X ◁ p) ≫ uncurry (𝟙 ((ihom X).obj (J.obj k))) = uncurry p := by
    rw [← uncurry_natural_left, Category.comp_id]
  rw [h₀, h₁]

/-- The point-set simplicial fiber over the full original traversal. -/
def fiber : ((ihom X).obj (J.obj k)).Subcomplex :=
  SSet.Subcomplex.fiber (graphMap T k f) (SSet.ihom₀Equiv.symm g)

private theorem range_curry_iff {Y : SSet.{0}} (p : X ⊗ Y ⟶ J.obj k) :
    SSet.Subcomplex.range (curry p) ≤ fiber T k f g ↔
      lift (fst X Y ≫ f) p ≫ (cylinder T).app k = fst X Y ≫ g := by
  rw [fiber, SSet.Subcomplex.range_le_fiber_iff]
  constructor
  · intro h
    simpa only [uncurry_graphMap, uncurry_curry, SSet.const_ihom₀Equiv_symm_apply] using
      congrArg uncurry h
  · intro h
    have hh : uncurry (curry p ≫ graphMap T k f) =
        uncurry (SSet.const (SSet.ihom₀Equiv.symm g)) := by
      rw [uncurry_graphMap, uncurry_curry, SSet.const_ihom₀Equiv_symm_apply, uncurry_curry, h]
    simpa only [curry_uncurry] using congrArg curry hh

/-- When one parameter lift exists, the exact parameter lift space of
the original reduced cylinder is trivially fibrant. -/
theorem toPoint_trivialFibration (t : X ⟶ J.obj k)
    (ht : lift f t ≫ (cylinder T).app k = g) :
    trivialFibrations SSet.{0}
      (SSet.stdSimplex.isTerminalObj₀.from (fiber T k f g : SSet.{0})) := by
  rw [← cofibrations_rlp]
  intro A Y j hj
  haveI : Cofibration j := (cofibration_iff j).2 hj
  haveI : Mono j := inferInstance
  constructor
  intro s u sq
  let F := fiber T k f g
  let p := uncurry (s ≫ F.ι)
  have hr : SSet.Subcomplex.range (curry p) ≤ F := by
    rw [curry_uncurry]
    exact (Subfunctor.range_comp_le _ _).trans_eq (SSet.Subcomplex.range_ι F)
  have hp := (range_curry_iff T k f g p).mp hr
  obtain ⟨q, hq₀, hq⟩ := JTGraphParameterRelative.extend_time j T k f g t ht p hp
  let l := SSet.Subcomplex.lift (curry q) ((range_curry_iff T k f g q).mpr hq)
  refine CommSq.HasLift.mk' ⟨l, ?_, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  apply (cancel_mono F.ι).mp
  rw [Category.assoc, SSet.Subcomplex.lift_ι, ← curry_natural_left, hq₀, curry_uncurry]

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport
open JTCommaGraphPredecessor (augmentationCode)

/-- The parameter space for the original native collapse of a specified
graph lift is trivially fibrant over the point. -/
theorem graphLift_toPoint_trivialFibration
    {W : SegalLocalizers.ReverseDaggerSpace.{0}} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    {P : Pres (W := W) (x := x) (y := y)} {S : NecklaceCode} (D : GraphLift P S) :
    trivialFibrations SSet.{0} (SSet.stdSimplex.isTerminalObj₀.from
      (fiber (code P) (degree P) (D.collapse ≫ augmentationCode P).map
        (D.collapse.map ≫ P.fiber.hom.right) : SSet.{0})) :=
  toPoint_trivialFibration (code P) (degree P) (D.collapse ≫ augmentationCode P).map
    (D.collapse.map ≫ P.fiber.hom.right) D.parameter D.comm

end

end DaggerModels.PartII.JTGraphParameterLiftSpace
