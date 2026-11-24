import DaggerModelsPartII.JTSimplexUnitKan
import DaggerModelsPartII.ParameterVertexLiftSpace
import DaggerModelsPartII.ProjectiveInjectiveComparison
import DaggerModelsPartII.JTProjectiveOrderedFiberComparison

/-!
# Extending the original ordinary coefficients to the groupoid parameter
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSimplexCoefficientExtension

open JTCylinderCEComparison JTParameterContraction JTProjectiveOrderedFiberComparison

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

theorem row_isFibrant (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (m : SimplexCategory) : IsFibrant (row W m) := by
  haveI : IsFibrant (W.obj (op (ReverseSimplex.inclusion.obj m))) :=
    (ProjectiveKanDiagram.model_isFibrant_iff ReverseSimplexᵒᵖ W).mp
      (ProjectiveInjectiveComparison.isFibrant_projective ReverseSimplexᵒᵖ W hW) _
  exact isFibrant_of_fibration (rowRestrictionIso W m).hom

/-- The specified coefficient, with the canonical terminal condition. -/
def extensionSquare (k : SimplexCategory) {X : SSet.{0}}
    (f : SSet.stdSimplex.obj k ⟶ X) :
    CommSq f (simplexUnit.app k) (terminal.from X)
      (terminal.from (GroupoidSimplex.parameter.obj k)) :=
  ⟨terminalIsTerminal.hom_ext _ _⟩

/-- A strict extension of the entire ordinary coefficient. -/
def extend (k : SimplexCategory) {X : SSet.{0}} [IsFibrant X]
    (f : SSet.stdSimplex.obj k ⟶ X) : GroupoidSimplex.parameter.obj k ⟶ X := by
  haveI := JTSimplexUnitKan.simplexUnit_cofibration k
  haveI := JTSimplexUnitKan.simplexUnit_weak k
  exact (extensionSquare k f).lift

theorem extend_restrict (k : SimplexCategory) {X : SSet.{0}} [IsFibrant X]
    (f : SSet.stdSimplex.obj k ⟶ X) : simplexUnit.app k ≫ extend k f = f := by
  haveI := JTSimplexUnitKan.simplexUnit_cofibration k
  haveI := JTSimplexUnitKan.simplexUnit_weak k
  unfold extend
  exact (extensionSquare k f).fac_left

theorem extend_vertex (k : SimplexCategory) {X : SSet.{0}} [IsFibrant X]
    (f : SSet.stdSimplex.obj k ⟶ X) (j : Fin (k.len + 1)) :
    parameterVertex k j ≫ extend k f =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k j) ≫ f := by
  rw [← JTParameterVertexKan.simplexUnit_vertex, Category.assoc, extend_restrict]

/-- The space of choices fixing the entire original coefficient is Kan. -/
theorem extensionSpace_kan (k : SimplexCategory) {X : SSet.{0}} [IsFibrant X]
    (f : SSet.stdSimplex.obj k ⟶ X) :
    (SSet.ihomToPullbackFiber (extensionSquare k f) : SSet.{0}).KanComplex := by
  haveI := JTSimplexUnitKan.simplexUnit_mono k
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (extensionSquare k f)

/-- The fixed-coefficient extension space is weakly contractible. -/
theorem extensionSpace_toPoint_weak (k : SimplexCategory) {X : SSet.{0}}
    [IsFibrant X] (f : SSet.stdSimplex.obj k ⟶ X) :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.ihomToPullbackFiber (extensionSquare k f))) := by
  haveI := JTSimplexUnitKan.simplexUnit_mono k
  haveI := JTSimplexUnitKan.simplexUnit_weak k
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak (extensionSquare k f)

end

end DaggerModels.PartII.JTSimplexCoefficientExtension
