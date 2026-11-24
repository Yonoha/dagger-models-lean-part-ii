import OrdinarySegalHorizontalCotensor
import DaggerModelsPartII.DiagramMappingPrecompFibration
import DaggerModelsPartII.JTSimplexUnitKan

/-!
# Actual rowwise Kan fibrations induced by parameter monomorphisms

At every original row, horizontal parameter restriction is the strict
mapping test for its tensor with that row's standard simplex. Such a tensor
is still monomorphic, so the existing injective mapping theorem gives a
Kan fibration. This asserts rowwise fibrations, not an injective fibration
of the whole cotensor restriction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorRestrictions

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (pre)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private theorem tensorRight_mono {K L : SSet.{0}} (f : K ⟶ L) [Mono f]
    (A : SSet.{0}) : Mono (f ▷ A) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro q
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  change (f.app q x.1, x.2) = (f.app q y.1, y.2) at h
  exact Prod.ext
    (((CategoryTheory.mono_iff_injective (f.app q)).mp inferInstance)
      (congrArg (fun p : L.obj q × A.obj q ↦ p.1) h))
    (congrArg (fun p : L.obj q × A.obj q ↦ p.2) h)

/-- A parameter monomorphism induces a Kan fibration on every exact row
of the original horizontal cotensor, without a Segal hypothesis. -/
theorem pre_app_fibration {K L : SSet.{0}} (f : K ⟶ L) [Mono f]
    (W : Space) [IsFibrant W] (n : SimplexCategory) :
    Fibration ((pre f W).app (op n)) := by
  have : Mono (f ▷ SSet.stdSimplex.obj n) := tensorRight_mono f _
  have : Mono (discrete.map (f ▷ SSet.stdSimplex.obj n)) :=
    OrdinaryCSSLocalization.discrete_map_mono _
  change Fibration (diagramMappingPrecomp
    (discrete.map (f ▷ SSet.stdSimplex.obj n)) W)
  exact InjectiveKanDiagram.diagramMappingPrecomp_isFibration SimplexCategoryᵒᵖ _ W

/-- The literal directed-edge restriction of walking-parameter cotensors
is a Kan fibration in each original row. -/
theorem simplexUnit_pre_app_fibration (W : Space) [IsFibrant W]
    (n : SimplexCategory) :
    Fibration ((pre (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W).app (op n)) := by
  have : Mono (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) :=
    JTSimplexUnitKan.simplexUnit_mono ⦋1⦌
  exact pre_app_fibration _ W n

#print axioms pre_app_fibration
#print axioms simplexUnit_pre_app_fibration

end

end DaggerModels.PartII.OrdinarySegalCotensorRestrictions
