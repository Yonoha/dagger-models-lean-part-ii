import DaggerModelsPartII.ResolutionGeneratorCofibrancy
import OriginalActualDaggerModelConstruction
import OriginalSmithSolutionsRecovered
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Cofibrant-source refinement of a Smith solution set

Each selected weak arrow is replaced by a weak arrow with the same target
and a cofibrant source. A square out of an original generating cofibration
factors through the replacement by a lift against its trivial-fibration
comparison. The original model and its `generatedJ` are unchanged.

This module establishes the refined solution-set interface. It does not
assert a cofibrant-domain theorem for the alternate Smith `J` family.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels

universe w v u

namespace DaggerModels.PartII.SmithCofibrantSourceSolution

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasInitial C]

private def sourceReplacement (a : Arrow C) :=
  MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to a.left)

/-- Replace only the source of an arrow by a cofibrant object. -/
def cofibrantSourceArrow (a : Arrow C) : Arrow C :=
  Arrow.mk ((sourceReplacement a).p ≫ a.hom)

/-- The replacement arrow maps to the original by a trivial fibration on sources. -/
def cofibrantSourceComparison (a : Arrow C) : cofibrantSourceArrow a ⟶ a :=
  Arrow.homMk (sourceReplacement a).p (𝟙 _) (by simp [cofibrantSourceArrow])

theorem cofibrantSourceArrow_source_cofibrant (a : Arrow C) :
    IsCofibrant (cofibrantSourceArrow a).left := by
  change IsCofibrant (sourceReplacement a).Z
  apply (isCofibrant_iff_of_isInitial (sourceReplacement a).i initialIsInitial).mpr
  exact (cofibration_iff _).mpr (sourceReplacement a).hi

theorem cofibrantSourceComparison_left_weak (a : Arrow C) :
    weakEquivalences C (cofibrantSourceComparison a).left :=
  (sourceReplacement a).hp.2

variable {I : MorphismProperty C}

/-- Refinement of a full-arrow Smith solution set when the testing maps have
cofibrant sources. The indexing types stay literally unchanged. -/
def refinedSolutionData
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I (weakEquivalences C))
    (hI : ∀ i : I.toSet, IsCofibrant i.1.left) :
    DaggerSmithSolutionSet.SolutionData.{w, v, u} I (weakEquivalences C) where
  index := S.index
  arrow i s := cofibrantSourceArrow (S.arrow i s)
  weak i s := by
    have hq : weakEquivalences C (sourceReplacement (S.arrow i s)).p :=
      (sourceReplacement (S.arrow i s)).hp.2
    exact (weakEquivalences C).comp_mem _ _ hq (S.weak i s)
  factor i f hf φ := by
    obtain ⟨s, α, β, hfac⟩ := S.factor i f hf φ
    let a := S.arrow i s
    let d := sourceReplacement a
    letI : IsCofibrant i.1.left := hI i
    haveI : HasLiftingProperty (initial.to i.1.left) d.p := by
      haveI : Cofibration (initial.to i.1.left) :=
        (isCofibrant_iff_of_isInitial (initial.to i.1.left) initialIsInitial).mp
          (hI i)
      haveI : Fibration d.p := (fibration_iff _).mpr d.hp.1
      haveI : WeakEquivalence d.p := (weakEquivalence_iff _).mpr d.hp.2
      infer_instance
    let sq : CommSq (initial.to d.Z) (initial.to i.1.left) d.p α.left :=
      CommSq.mk (initialIsInitial.hom_ext _ _)
    let α' : i.1 ⟶ cofibrantSourceArrow a :=
      Arrow.homMk sq.lift α.right (by
        change sq.lift ≫ (d.p ≫ a.hom) = i.1.hom ≫ α.right
        rw [← Category.assoc, sq.fac_right]
        exact Arrow.w α)
    let β' : cofibrantSourceArrow a ⟶ f := cofibrantSourceComparison a ≫ β
    refine ⟨s, α', β', ?_⟩
    have hα : α' ≫ cofibrantSourceComparison a = α := by
      apply Arrow.hom_ext
      · change sq.lift ≫ d.p = α.left
        exact sq.fac_right
      · change α.right ≫ 𝟙 _ = α.right
        simp
    calc
      α' ≫ β' = (α' ≫ cofibrantSourceComparison a) ≫ β := by
        simp only [β', Category.assoc]
      _ = α ≫ β := by rw [hα]
      _ = φ := hfac

theorem refinedSolutionData_source_cofibrant
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I (weakEquivalences C))
    (hI : ∀ i : I.toSet, IsCofibrant i.1.left)
    (i : I.toSet) (s : S.index i) :
    IsCofibrant ((refinedSolutionData S hI).arrow i s).left :=
  cofibrantSourceArrow_source_cofibrant (S.arrow i s)

end

end DaggerModels.PartII.SmithCofibrantSourceSolution

namespace DaggerModels.PartII.SmithCofibrantSourceSolution

noncomputable section

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerOriginalJoyalModel.standardModelCategory.{0}

/-- Every source of the literal original boundary-generating family is cofibrant. -/
theorem originalID_source_cofibrant
    (i : DaggerActualWeakAccessibility.originalID.{0}.toSet) :
    IsCofibrant i.1.left := by
  have he : DaggerActualWeakAccessibility.originalID.{0} =
      DaggerModels.freeBoundaryGenerators DaggerModels.freeDagger.{0} :=
    DaggerActualWeakAccessibility.originalID_eq
  have hi : DaggerModels.freeBoundaryGenerators DaggerModels.freeDagger.{0} i.1.hom := by
    rw [← he]
    exact i.property
  change ofHoms (fun n : ℕ ↦
    DaggerModels.freeDagger.map (SSet.boundary.{0} n).ι) i.1.hom at hi
  obtain ⟨n, h⟩ := (ofHoms_iff _ i.1.hom).mp hi
  have hA : i.1.left =
      DaggerModels.freeDagger.obj (SSet.boundary.{0} n).toSSet :=
    congrArg (fun a : Arrow DaggerSSet.{0} ↦ a.left) h
  rw [hA]
  exact freeDagger_isCofibrant _

/-- The fixed original solution set, viewed in the actual standard dagger Joyal model. -/
def standardSolutionAsModelWeak :
    DaggerSmithSolutionSet.SolutionData
      DaggerActualWeakAccessibility.originalID.{0}
      (weakEquivalences DaggerSSet.{0}) := by
  change DaggerSmithSolutionSet.SolutionData
    DaggerActualWeakAccessibility.originalID.{0}
    DaggerOriginalJoyalModel.standardModelCategory.{0}.categoryWithWeakEquivalences.weakEquivalences
  rw [DaggerOriginalJoyalModel.model_weak DaggerUnitaryInvariance.standardReplacement]
  exact DaggerActualWeakAccessibility.solution
    DaggerUnitaryInvariance.standardReplacement

/-- The original solution set with each selected source replaced by a cofibrant one. -/
def standardRefinedSolution :
    DaggerSmithSolutionSet.SolutionData
      DaggerActualWeakAccessibility.originalID.{0}
      (weakEquivalences DaggerSSet.{0}) :=
  refinedSolutionData standardSolutionAsModelWeak originalID_source_cofibrant

/-- Its chosen weak arrows have cofibrant sources, without claiming this for
the old `generatedJ`. -/
theorem standardRefinedSolution_source_cofibrant
    (i : DaggerActualWeakAccessibility.originalID.{0}.toSet)
    (s : standardRefinedSolution.index i) :
    IsCofibrant (standardRefinedSolution.arrow i s).left :=
  refinedSolutionData_source_cofibrant
    standardSolutionAsModelWeak originalID_source_cofibrant i s

end

end DaggerModels.PartII.SmithCofibrantSourceSolution
