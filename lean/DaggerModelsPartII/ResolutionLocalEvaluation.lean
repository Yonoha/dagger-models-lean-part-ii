import DaggerModelsPartII.CosimplicialQuillenComparison
import DaggerModelsPartII.ResolutionGeneratorCofibrancy
import DaggerModelsPartII.ResolutionLocality

/-! The resolution local test in each outer degree. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localEvaluationLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localEvaluationColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localEvaluationCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance localEvaluationReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

private def tensorOperator {i j : ℕ} (f : ⦋i⦌ ⟶ ⦋j⦌) :
    externalTensorWith (Δ[i] : SSet.{u}) ⟶ externalTensorWith Δ[j] :=
  Functor.whiskerLeft _ ((Functor.whiskeringLeft _ _ _).map (SSet.stdSimplex.map f))

private def evaluationOperator {i j : ℕ} (f : ⦋i⦌ ⟶ ⦋j⦌) :
    evaluationAt.{u} j ⟶ evaluationAt i :=
  (evaluation _ _).map f.op

private theorem evaluationOperator_mate {i j : ℕ} (f : ⦋i⦌ ⟶ ⦋j⦌)
    {A : DaggerSSet.{u}} {W : ResolutionDiagram.{u}}
    (q : (externalTensorWith (Δ[j] : SSet.{u})).obj A ⟶ W) :
    (evaluationAdjunction i).homEquiv A W ((tensorOperator f).app A ≫ q) =
      (evaluationAdjunction j).homEquiv A W q ≫ (evaluationOperator f).app W := by
  simp only [evaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change SSet.yonedaEquiv ((externalTensorAdjunction A).homEquiv Δ[i] W
    ((externalTensor A).map (SSet.stdSimplex.map f) ≫ q)) = _
  rw [Adjunction.homEquiv_naturality_left]
  let z := (externalTensorAdjunction A).homEquiv Δ[j] W q
  change SSet.yonedaEquiv (SSet.stdSimplex.map f ≫ z) =
    ((mappingSimplicialSet A).obj W).map f.op (SSet.yonedaEquiv z)
  exact (uliftYonedaEquiv_naturality z f.op).symm

/-- The outer simplex operator is tested by the induced coefficient map on derived mapping
simplicial sets. -/
theorem resolutionOuterOperator_mapping_iff {i j : ℕ} (f : ⦋i⦌ ⟶ ⦋j⦌)
    (A : DaggerSSet.{u}) [IsCofibrant A] (R : CosimplicialResolution A)
    (W : ResolutionDiagram.{u}) [IsFibrant W] :
    homotopyMappingWeakEquivalences W ((externalTensor A).map (SSet.stdSimplex.map f)) ↔
      weakEquivalences SSet.{u} (R.mappingSSet.map (W.map f.op)) := by
  letI := evaluationAdjunction_isQuillen.{u} i
  letI := evaluationAdjunction_isQuillen.{u} j
  exact homotopyMappingWeakEquivalences_of_mates (evaluationAdjunction i) (evaluationAdjunction j)
    (tensorOperator f) (evaluationOperator f) (fun q ↦ evaluationOperator_mate f q) R W

/-- The local-object test is a test on the collapse maps in the coefficient category. -/
theorem resolutionLocalObject_iff_coefficientMapping (W : ResolutionDiagram.{u}) :
    resolutionLocalObject W ↔ IsFibrant W ∧
      ∀ (n : ℕ) (simplex : Bool) (k : ℕ),
        weakEquivalences SSet.{u}
          ((cosimplicialResolution (resolutionTestObject.{u} n simplex)).mappingSSet.map
            (W.map (simplexCollapse (op ⦋k + 1⦌)).op)) := by
  rw [resolutionLocalObject_iff]
  constructor <;> rintro ⟨hw, h⟩ <;> refine ⟨hw, ?_⟩
  · letI := hw
    intro n simplex k
    let A := resolutionTestObject.{u} n simplex
    letI : IsCofibrant A := freeDagger_isCofibrant _
    exact (resolutionOuterOperator_mapping_iff (simplexCollapse (op ⦋k + 1⦌))
      A (cosimplicialResolution A) W).mp (h n simplex k)
  · letI := hw
    intro n simplex k
    let A := resolutionTestObject.{u} n simplex
    letI : IsCofibrant A := freeDagger_isCofibrant _
    exact (resolutionOuterOperator_mapping_iff (simplexCollapse (op ⦋k + 1⦌))
      A (cosimplicialResolution A) W).mpr (h n simplex k)

/-- A Reedy fibrant, homotopically constant diagram is local for the literal family. -/
theorem resolutionLocalObject_of_homotopicallyConstant (W : ResolutionDiagram.{u}) [IsFibrant W]
    (h : reedyWeakEquivalences (resolutionCounit W)) : resolutionLocalObject W := by
  apply (resolutionLocalObject_iff_coefficientMapping W).mpr
  refine ⟨inferInstance, ?_⟩
  intro n simplex k
  letI := reedyFibrant_obj W (op ⦋0⦌)
  letI := reedyFibrant_obj W (op ⦋k + 1⦌)
  exact (cosimplicialResolution (resolutionTestObject.{u} n simplex)).mappingSSet_map_weak
    (W.map (simplexCollapse (op ⦋k + 1⦌)).op) (h _)

end

end DaggerModels.PartII
