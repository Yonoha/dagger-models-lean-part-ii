import DaggerModelsPartII.ExternalTensorBox
import DaggerModelsPartII.ResolutionLocalCharacterization
import DaggerModelsPartII.ReedyCombinatorial
import Mathlib.Logic.Small.Set

/-! The free dagger boundary boxes against the zeroth outer vertex. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open DaggerModels

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localVertexLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localVertexColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localVertexModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance localVertexReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

/-- The zeroth vertex in a positive-degree outer simplex. -/
def resolutionZeroVertex (k : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[k + 1] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0)

instance (k : ℕ) : Mono (resolutionZeroVertex.{u} k) := by
  have h : resolutionZeroVertex.{u} k ≫
      SSet.stdSimplex.map (simplexCollapse (op ⦋k + 1⦌)) = 𝟙 _ := by
    rw [resolutionZeroVertex, ← SSet.stdSimplex.map_comp]
    rw [show SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0 ≫
      simplexCollapse (op ⦋k + 1⦌) = 𝟙 _ from SimplexCategory.isTerminalZero.hom_ext _ _]
    exact SSet.stdSimplex.{u}.map_id _
  exact mono_of_mono_fac h

private theorem tensor_vertex_local (n : ℕ) (simplex : Bool) (k : ℕ) :
    resolutionLocalEquivalences
      ((externalTensor (resolutionTestObject.{u} n simplex)).map (resolutionZeroVertex k)) :=
  (tensorCollapseTests_iff_allOperators (resolutionTestObject n simplex) resolutionLocalEquivalences).mp
    (fun m ↦ resolutionGenerators_le_localEquivalences _ ⟨(n, simplex, m)⟩)
    0 (k + 1) (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0)

/-- The free dagger boundary in degree (n) boxed with the zeroth outer vertex. -/
def resolutionLocalVertexBox (n k : ℕ) :=
  externalTensorBox (freeDagger.{u}.map (SSet.boundary n).ι) (resolutionZeroVertex k)

/-- The small family of free dagger boundary boxes used for local fibrant replacement. -/
def resolutionLocalVertexGenerators : MorphismProperty ResolutionDiagram.{u} :=
  ofHoms (fun (p : ℕ × ℕ) ↦ resolutionLocalVertexBox p.1 p.2)

instance : IsSmall.{u} resolutionLocalVertexGenerators.{u} := isSmall_ofHoms _

/-- Each vertex box is both a Reedy cofibration and a local equivalence. -/
theorem resolutionLocalVertexGenerators_le :
    resolutionLocalVertexGenerators.{u} ≤ reedyCofibrations ⊓ resolutionLocalEquivalences := by
  intro X Y f hf
  obtain ⟨⟨n, k⟩⟩ := hf
  have hi : cofibrations DaggerSSet.{u} (freeDagger.map (SSet.boundary n).ι) := by
    change DaggerOriginalJoyalModel.standardModelCategory.categoryWithCofibrations.cofibrations _
    rw [DaggerOriginalJoyalModel.standard_model_cof]
    exact freeDagger_map_isFreeCofibration _
  refine ⟨externalTensorBox_cofibration _ _ hi, ?_⟩
  letI := freeDagger_isCofibrant (SSet.boundary.{u} n).toSSet
  exact externalTensorBox_localEquivalence _ _
    ⟨externalTensor_map_cofibration _, tensor_vertex_local n false k⟩
    (tensor_vertex_local n true k)

private theorem resolutionLocalVertexGenerators_rlp_terminal (W : ResolutionDiagram.{u}) :
    resolutionLocalVertexGenerators.rlp (terminal.from W) ↔
      ∀ k : ℕ, trivialFibrations DaggerSSet.{u}
        (W.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0).op) := by
  have hI : (DaggerModels.freeBoundaryGenerators DaggerModels.freeDagger.{u}).rlp =
      trivialFibrations DaggerSSet.{u} := by
    have he : DaggerActualWeakAccessibility.originalID.{u} =
        DaggerModels.freeBoundaryGenerators DaggerModels.freeDagger.{u} :=
      DaggerActualWeakAccessibility.originalID_eq
    rw [← he]
    exact (DaggerOriginalJoyalModel.model_trivialFibrations
      DaggerUnitaryInvariance.standardReplacement).symm
  simp only [← hI]
  constructor
  · intro h k A B i hi
    obtain ⟨n⟩ := hi
    exact (externalTensorBox_hasLiftingProperty_terminal_iff _ _ W).mp
      (h (resolutionLocalVertexBox n k) ⟨(n, k)⟩)
  · intro h A B i hi
    obtain ⟨⟨n, k⟩⟩ := hi
    exact (externalTensorBox_hasLiftingProperty_terminal_iff _ _ W).mpr
      (h k (freeDagger.map (SSet.boundary n).ι) ⟨n⟩)

private theorem resolutionVertex_fibration (W : ResolutionDiagram.{u}) [IsFibrant W] (k : ℕ) :
    fibrations DaggerSSet.{u} (W.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0).op) := by
  letI : HasLimitsOfSize.{0, u} DaggerSSet.{u} := hasLimitsOfSizeShrink.{0, u} _
  let j := resolutionZeroVertex.{u} k
  have h := diagramRestrictionPre_fibration W j
  have w := diagramRestrictionSimplexIso_natural W (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0)
  apply ((fibrations DaggerSSet.{u}).cancel_left_of_respectsIso
    (diagramRestrictionSimplexIso W (k + 1)).hom _).mp
  rw [← w]
  exact ((fibrations DaggerSSet.{u}).cancel_right_of_respectsIso
    (diagramRestrictionPre j W) (diagramRestrictionSimplexIso W 0).hom).mpr h

private theorem resolutionVertex_collapse_comp (W : ResolutionDiagram.{u}) (k : ℕ) :
    (resolutionCounit W).app (op ⦋k + 1⦌) ≫
      W.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0).op = 𝟙 _ := by
  change W.map (simplexCollapse (op ⦋k + 1⦌)).op ≫
    W.map (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0).op = _
  rw [← W.map_comp, ← op_comp]
  have h : SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0 ≫
      simplexCollapse (op ⦋k + 1⦌) = 𝟙 _ := SimplexCategory.isTerminalZero.hom_ext _ _
  rw [h, op_id, W.map_id]
  rfl

/-- A small family which detects the exact local fibrant objects by right lifting. -/
def resolutionLocalFibrancyGenerators : MorphismProperty ResolutionDiagram.{u} :=
  resolutionReedyJ ⊔ resolutionLocalVertexGenerators

instance : IsSmall.{u} resolutionLocalFibrancyGenerators.{u} := by
  constructor
  change Small.{u} (resolutionReedyJ.{u}.toSet ∪ resolutionLocalVertexGenerators.{u}.toSet :
    Set (Arrow ResolutionDiagram.{u}))
  infer_instance

theorem resolutionLocalFibrancyGenerators_le :
    resolutionLocalFibrancyGenerators.{u} ≤ reedyCofibrations ⊓ resolutionLocalEquivalences := by
  refine sup_le ?_ resolutionLocalVertexGenerators_le
  have hJ : resolutionReedyJ.{u} ≤ trivialCofibrations ResolutionDiagram.{u} := by
    rw [← llp_eq_of_wfs (trivialCofibrations ResolutionDiagram.{u}) (fibrations ResolutionDiagram.{u}),
      ← resolutionReedyJ_rlp]
    exact le_llp_rlp _
  exact hJ.trans (inf_le_inf_left _ reedyWeakEquivalences_le_resolutionLocalEquivalences)

/-- A diagram is (S_h)-local precisely when its terminal map lifts against the
original Reedy trivial generators and the free dagger boundary vertex boxes. -/
theorem resolutionLocalObject_iff_rlp (W : ResolutionDiagram.{u}) :
    resolutionLocalObject W ↔ resolutionLocalFibrancyGenerators.rlp (terminal.from W) := by
  have hrlp : resolutionLocalFibrancyGenerators.rlp (terminal.from W) ↔
      IsFibrant W ∧ resolutionLocalVertexGenerators.rlp (terminal.from W) := by
    constructor
    · intro h
      have hJ := antitone_rlp
        (show resolutionReedyJ.{u} ≤ resolutionLocalFibrancyGenerators from le_sup_left) _ h
      rw [resolutionReedyJ_rlp] at hJ
      exact ⟨(fibration_iff _).mpr hJ, antitone_rlp
        (show resolutionLocalVertexGenerators.{u} ≤ resolutionLocalFibrancyGenerators from le_sup_right) _ h⟩
    · rintro ⟨hW, hV⟩
      have hJ : resolutionReedyJ.rlp (terminal.from W) := by
        rw [resolutionReedyJ_rlp]
        exact (fibration_iff _).mp hW
      intro A B f hf
      rcases hf with hf | hf
      · exact hJ f hf
      · exact hV f hf
  rw [hrlp, resolutionLocalObject_iff_homotopicallyConstant,
    resolutionLocalVertexGenerators_rlp_terminal]
  constructor
  · rintro ⟨hf, hc⟩
    letI := hf
    refine ⟨hf, fun k ↦ ⟨resolutionVertex_fibration W k, ?_⟩⟩
    apply (weakEquivalences DaggerSSet.{u}).of_precomp _ _ (hc (op ⦋k + 1⦌))
    rw [resolutionVertex_collapse_comp]
    exact (weakEquivalences DaggerSSet.{u}).id_mem _
  · rintro ⟨hf, hv⟩
    refine ⟨hf, ?_⟩
    intro j
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = j :=
      ⟨j.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
    cases n with
    | zero =>
      change weakEquivalences DaggerSSet.{u} (W.map (simplexCollapse (op ⦋0⦌)).op)
      rw [simplexCollapse_zero_op, W.map_id]
      exact (weakEquivalences DaggerSSet.{u}).id_mem _
    | succ k =>
      apply (weakEquivalences DaggerSSet.{u}).of_postcomp _ _ (hv k).2
      rw [resolutionVertex_collapse_comp]
      exact (weakEquivalences DaggerSSet.{u}).id_mem _

end

end DaggerModels.PartII
