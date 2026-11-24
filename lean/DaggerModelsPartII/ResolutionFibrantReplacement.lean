import DaggerModelsPartII.ReedyCombinatorial
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-! Functorial fibrant replacement for the Reedy model. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance replacementCoefficientLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance replacementCoefficientColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance replacementCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance replacementReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

private def resolutionReedyFibrantFactorization :
    FunctorialFactorizationData (trivialCofibrations ResolutionDiagram.{u})
      (fibrations ResolutionDiagram.{u}) := by
  letI := resolutionDiagramLocallyPresentable.{u}
  rw [← llp_eq_of_wfs (trivialCofibrations ResolutionDiagram.{u})
    (fibrations ResolutionDiagram.{u}), ← resolutionReedyJ_rlp]
  exact DaggerSmithSolutionSet.soaFactorization resolutionReedyJ

/-- The terminal maps, regarded as a diagram in the arrow category. -/
def resolutionTerminalArrow : ResolutionDiagram.{u} ⥤ Arrow ResolutionDiagram.{u} where
  obj W := Arrow.mk (terminal.from W)
  map f := Arrow.homMk f (𝟙 _) (terminalIsTerminal.hom_ext _ _)
  map_id _ := by apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by
    apply Arrow.hom_ext
    · rfl
    · exact (Category.id_comp _).symm

/-- Fibrant replacement obtained from the Reedy generating trivial cofibrations. -/
def resolutionReedyFibrantReplacement : ResolutionDiagram.{u} ⥤ ResolutionDiagram.{u} :=
  resolutionTerminalArrow ⋙ resolutionReedyFibrantFactorization.Z

/-- The Reedy fibrant replacement map is natural in the diagram. -/
def resolutionReedyFibrantReplacementUnit :
    𝟭 ResolutionDiagram.{u} ⟶ resolutionReedyFibrantReplacement :=
  Functor.whiskerLeft resolutionTerminalArrow resolutionReedyFibrantFactorization.i

theorem resolutionReedyFibrantReplacementUnit_trivialCofibration (W : ResolutionDiagram.{u}) :
    trivialCofibrations ResolutionDiagram.{u} (resolutionReedyFibrantReplacementUnit.app W) :=
  resolutionReedyFibrantFactorization.hi (resolutionTerminalArrow.obj W)

theorem resolutionReedyFibrantReplacement_isFibrant (W : ResolutionDiagram.{u}) :
    IsFibrant (resolutionReedyFibrantReplacement.obj W) :=
  (isFibrant_iff_of_isTerminal _ terminalIsTerminal).mpr
    ((fibration_iff _).mpr
      (resolutionReedyFibrantFactorization.hp (resolutionTerminalArrow.obj W)))

/-- A diagram levelwise weakly equivalent from a constant diagram is homotopically constant. -/
theorem resolutionCounit_weak_of_constant_weak {A : DaggerSSet.{u}} {W : ResolutionDiagram.{u}}
    (q : constantDiagram.obj A ⟶ W) (hq : reedyWeakEquivalences q) :
    reedyWeakEquivalences (resolutionCounit W) := by
  intro k
  have h := q.naturality (simplexCollapse k).op
  change 𝟙 A ≫ q.app k = q.app (op ⦋0⦌) ≫ (resolutionCounit W).app k at h
  rw [Category.id_comp] at h
  exact (weakEquivalences DaggerSSet.{u}).of_precomp
    (q.app (op ⦋0⦌)) ((resolutionCounit W).app k) (hq (op ⦋0⦌)) (h ▸ hq k)

/-- The Reedy fibrant replacement of a constant diagram remains homotopically constant. -/
theorem resolutionReedyFibrantReplacement_constant_counit_weak (A : DaggerSSet.{u}) :
    reedyWeakEquivalences
      (resolutionCounit (resolutionReedyFibrantReplacement.obj (constantDiagram.obj A))) :=
  resolutionCounit_weak_of_constant_weak _
    (resolutionReedyFibrantReplacementUnit_trivialCofibration (constantDiagram.obj A)).2

end

end DaggerModels.PartII
