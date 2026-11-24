import DaggerModelsPartII.JTSimplexCoefficientExtension
import DaggerModelsPartII.JTRowRealizationGenerator
import DaggerModelsPartII.NormalizedTwoBeadRawRefinement

/-!
# The original target refinement for an ordinary zero-row edge coefficient

The target map is determined by the original ordinary coefficient. Its
proof uses the full restriction equation of an auxiliary groupoid extension.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTZeroRowSimplexRefinement

open JTProjectiveOrderedFiberComparison JTSimplexCoefficientExtension
open JTCylinderCEComparison JTParameterContraction JTRowRealizationGenerator
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

/-- The raw edge on the literal coend box associated to the ordinary coefficient. -/
def rawEdge (W : Source) (f : (Δ[1] : SSet.{0}) ⟶ row W ⦋0⦌) :
    (Δ[1] : SSet.{0}) ⟶ R W :=
  simplexUnit.app ⦋1⦌ ≫
    CartesianMonoidalCategory.lift
        (SSet.stdSimplex.isTerminalObj₀.from J) (𝟙 J) ≫
      JTRealizationGenerators.generator (JTReversalInput.ordinaryInput.obj W)
        (⦋0⦌, ⦋1⦌) (SSet.yonedaEquiv (X := row W ⦋0⦌) f)

/-- The two constructions agree as complete simplicial maps for any strict
extension of the coefficient. -/
theorem rawEdge_eq_of_extension (W : Source)
    (f : (Δ[1] : SSet.{0}) ⟶ row W ⦋0⦌) (z : J ⟶ row W ⦋0⦌)
    (h : simplexUnit.app ⦋1⦌ ≫ z = f) :
    JTZeroRowParameterEdge.rawEdge W z = rawEdge W f := by
  have hlabel : JTZeroRowParameterEdge.zeroRowLabel W z =
      rowCoefficient W 0 ⦋1⦌ (SSet.yonedaEquiv (X := row W ⦋0⦌) f) := by
    unfold JTZeroRowParameterEdge.zeroRowLabel
    rw [← Category.assoc, h, SSet.yonedaEquiv_comp]
    rfl
  unfold JTZeroRowParameterEdge.rawEdge JTZeroRowParameterEdge.zeroRowParameterMap rawEdge
  rw [hlabel, realizedRowCoefficient_eq_generator]

/-- On a vertical edge of an original zero-row box whose parameter comes
from a simplex operator, the full map is the restricted original generator. -/
theorem rawEdge_eq_generator_restriction (W : Source) {k : SimplexCategory}
    (α : ⦋1⦌ ⟶ k) (f : SSet.stdSimplex.obj k ⟶ row W ⦋0⦌) :
    rawEdge W (SSet.stdSimplex.map α ≫ f) =
      simplexUnit.app ⦋1⦌ ≫
        CartesianMonoidalCategory.lift (SSet.stdSimplex.isTerminalObj₀.from J)
          (GroupoidSimplex.parameter.map α) ≫
        JTRealizationGenerators.generator (JTReversalInput.ordinaryInput.obj W)
          (⦋0⦌, k) (SSet.yonedaEquiv (X := row W ⦋0⦌) f) := by
  let a : (⦋0⦌, ⦋1⦌) ⟶ (⦋0⦌, k) := (𝟙 _, α)
  let u : J ⟶ (Δ[0] : SSet.{0}) ⊗ J :=
    CartesianMonoidalCategory.lift (SSet.stdSimplex.isTerminalObj₀.from J) (𝟙 J)
  have h := JTRealizationGenerators.generator_relation
    (JTReversalInput.ordinaryInput.obj W) a (SSet.yonedaEquiv (X := row W ⦋0⦌) f)
  rw [OrdinaryJTRealization.tFunctor_map] at h
  change (SSet.stdSimplex.map (𝟙 ⦋0⦌) ⊗ₘ GroupoidSimplex.parameter.map α) ≫ _ =
    JTRealizationGenerators.generator (JTReversalInput.ordinaryInput.obj W)
      (⦋0⦌, ⦋1⦌) ((row W ⦋0⦌).map α.op (SSet.yonedaEquiv (X := row W ⦋0⦌) f)) at h
  rw [CategoryTheory.Functor.map_id, ← SSet.yonedaEquiv_map_comp] at h
  have hg : u ≫ (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ GroupoidSimplex.parameter.map α) =
      CartesianMonoidalCategory.lift (SSet.stdSimplex.isTerminalObj₀.from J)
        (GroupoidSimplex.parameter.map α) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [u, Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst, Category.comp_id]
    · simp only [u, Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc, CartesianMonoidalCategory.lift_snd, Category.id_comp]
  unfold rawEdge
  change simplexUnit.app ⦋1⦌ ≫ u ≫ _ = _
  rw [← h, ← Category.assoc u, hg]

private def extendPath (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (f : (Δ[1] : SSet.{0}) ⟶ row W ⦋0⦌) : J ⟶ row W ⦋0⦌ := by
  haveI := row_isFibrant W hW ⦋0⦌
  exact extend ⦋1⦌ f

private theorem extendPath_restrict (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (f : (Δ[1] : SSet.{0}) ⟶ row W ⦋0⦌) :
    simplexUnit.app ⦋1⦌ ≫ extendPath W hW f = f := by
  haveI := row_isFibrant W hW ⦋0⦌
  exact extend_restrict ⦋1⦌ f

variable (W : Source)
variable (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
variable (f : (Δ[1] : SSet.{0}) ⟶ row W ⦋0⦌)
variable (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
variable (hx : SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) ≫ f = vertexPoint W x)
variable (hy : SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) ≫ f = vertexPoint W y)

private theorem pathVertex (i : Fin 2)
    (v : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hv : SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) ≫ f = vertexPoint W v) :
    parameterVertex ⦋1⦌ i ≫ extendPath W hW f = vertexPoint W v := by
  rw [← JTParameterVertexKan.simplexUnit_vertex, Category.assoc, extendPath_restrict, hv]

private def extendedTarget :=
  JTZeroRowParameterEdge.rawNecklaceOver W x y (extendPath W hW f)
    (pathVertex W hW f 0 x hx) (pathVertex W hW f 1 y hy)

/-- The same native one-bead code with the coend map of the specified ordinary coefficient. -/
def rawNecklaceOver :
    NecklacesOver (R W)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y) where
  code := single 1
  map := (singleIso 1).hom ≫ rawEdge W f
  first := by
    rw [← rawEdge_eq_of_extension W f (extendPath W hW f) (extendPath_restrict W hW f)]
    exact (extendedTarget W hW f x y hx hy).first
  last := by
    rw [← rawEdge_eq_of_extension W f (extendPath W hW f) (extendPath_restrict W hW f)]
    exact (extendedTarget W hW f x y hx hy).last

/-- The same target comma is inhabited for the specified ordinary coefficient. -/
def targetCommaObject :
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y)
      (rawNecklaceOver W hW f x y hx hy) := by
  let q := NormalizedTwoBeadRawRefinement.chosenRawTargetCommaObject W hW
    (extendPath W hW f) x y (pathVertex W hW f 0 x hx) (pathVertex W hW f 1 y hy)
  let e : extendedTarget W hW f x y hx hy ⟶ rawNecklaceOver W hW f x y hx hy :=
    { hom := 𝟙 (single 1)
      w := by
        change (𝟙 (single 1).toSSet) ≫ ((singleIso 1).hom ≫ rawEdge W f) =
          (singleIso 1).hom ≫ JTZeroRowParameterEdge.rawEdge W (extendPath W hW f)
        rw [Category.id_comp, rawEdge_eq_of_extension W f _ (extendPath_restrict W hW f)] }
  exact CostructuredArrow.mk (q.hom ≫ e)

end

end DaggerModels.PartII.JTZeroRowSimplexRefinement
