import DaggerModelsPartII.JTGraphInterpolatedSourceComparison
import DaggerModelsPartII.NecklaceCylinderJointDiagram

/-! The joint diagram of original cylinder fibers and its weak equivalences. -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphCylinderFiberDiagram

open BoundaryNecklaceComma (necklaceUnder)
open JTGraphInterpolatedComparison (Fiber)
open JTGraphInterpolatedSourceComparison (sourceMap sourceMap_time)
open JTNecklaceEndpointCylinder (under)

noncomputable section

/-- The original necklace fibers form a joint diagram in the native source and time. -/
def diagram : NecklaceCode × SimplexCategory ⥤ Cat.{0, 0} :=
  NecklaceCylinderJointDiagram.cylinderUnder ⋙ BoundaryNecklaceComma.diagram

variable {R S : NecklaceCode} {m n : SimplexCategory}

/-- The action of an original source and time operator on the whole fiber. -/
def joint (g : R ⟶ S) (θ : m ⟶ n) : Fiber R m ⥤ Fiber S n :=
  (diagram.map (X := (R, m)) (Y := (S, n)) (g, θ)).toFunctor

private theorem cylinder_map (g : R ⟶ S) (θ : m ⟶ n) :
    NecklaceCylinderJointDiagram.cylinderUnder.map (X := (R, m)) (Y := (S, n)) (g, θ) =
      sourceMap g m ≫ (under S).map θ := by
  apply Under.UnderMorphism.ext
  rfl

private theorem map_comp {A B C : Under JTXiEndpointCollapse.boundary}
    (u : A ⟶ B) (v : B ⟶ C) :
    CostructuredArrow.map (S := necklaceUnder) (u ≫ v) =
      CostructuredArrow.map u ⋙ CostructuredArrow.map v :=
  congrArg Cat.Hom.toFunctor (BoundaryNecklaceComma.diagram.map_comp u v)

/-- A joint map is native source change followed by time change. -/
theorem joint_source_time (g : R ⟶ S) (θ : m ⟶ n) :
    joint g θ = CostructuredArrow.map (sourceMap g m) ⋙
      CostructuredArrow.map ((under S).map θ) := by
  change CostructuredArrow.map (S := necklaceUnder)
    (NecklaceCylinderJointDiagram.cylinderUnder.map (X := (R, m)) (Y := (S, n)) (g, θ)) = _
  rw [cylinder_map]
  exact map_comp _ _

/-- The same joint map is also time change followed by native source change. -/
theorem joint_time_source (g : R ⟶ S) (θ : m ⟶ n) :
    joint g θ = CostructuredArrow.map ((under R).map θ) ⋙
      CostructuredArrow.map (sourceMap g n) := by
  change CostructuredArrow.map (S := necklaceUnder)
    (NecklaceCylinderJointDiagram.cylinderUnder.map (X := (R, m)) (Y := (S, n)) (g, θ)) = _
  rw [cylinder_map, sourceMap_time]
  exact map_comp _ _

/-- The two paths around an original source-time square are equal as functors. -/
theorem source_time (g : R ⟶ S) (θ : m ⟶ n) :
    CostructuredArrow.map (S := necklaceUnder) (sourceMap g m) ⋙
        CostructuredArrow.map ((under S).map θ) =
      CostructuredArrow.map ((under R).map θ) ⋙ CostructuredArrow.map (sourceMap g n) :=
  (joint_source_time g θ).symm.trans (joint_time_source g θ)

/-- Any functor between two complete cylinder fibers has Kan weak nerve. -/
theorem fiber_map_weak (F : Fiber R m ⥤ Fiber S n) : WeakEquivalence (nerveMap F) := by
  let p := pointMap (nerve (Fiber S n))
  have hp : WeakEquivalence p := (weakEquivalence_iff_GW p).mpr
    (JTHomotopyTargetComma.fiber_point_GW_at S n)
  have h : nerveMap F ≫ p = pointMap (nerve (Fiber R m)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_postcomp_iff (nerveMap F) p).mp
  rw [h]
  exact (weakEquivalence_iff_GW _).mpr (JTHomotopyTargetComma.fiber_point_GW_at R m)

/-- Both legs from a common restricted source fiber are Kan weak on nerves. -/
theorem comparison_span_weak (g : R ⟶ S) (θ : m ⟶ n) :
    WeakEquivalence (nerveMap (CostructuredArrow.map (S := necklaceUnder) ((under R).map θ))) ∧
    WeakEquivalence (nerveMap (CostructuredArrow.map (S := necklaceUnder) (sourceMap g m))) :=
  ⟨fiber_map_weak _, fiber_map_weak _⟩

end

end DaggerModels.PartII.JTGraphCylinderFiberDiagram
