import DaggerModelsPartII.LocalVertexGenerators
import DaggerModelsPartII.ResolutionLocalComparison
import DaggerModelsPartII.SourceResolutionTowerConstruction
import CoproductCellSerialization
import OriginalSOAFactorizationRecovered
import DaggerModelsPartII.ArrowAccessibility

/-! Functorial replacement with values in the exact local fibrant objects. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localReplacementLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localReplacementColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localReplacementCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance localReplacementReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

private structure LocalGeneratorRank where
  κ : Cardinal.{u}
  regular : κ.IsRegular
  left : ∀ r : resolutionLocalFibrancyGenerators.{u}.toSet,
    @IsCardinalPresentable _ _ r.1.left κ ⟨regular⟩
  right : ∀ r : resolutionLocalFibrancyGenerators.{u}.toSet,
    @IsCardinalPresentable _ _ r.1.right κ ⟨regular⟩

private def localGeneratorRank : LocalGeneratorRank.{u} := by
  letI := resolutionDiagramLocallyPresentable.{u}
  let T := resolutionLocalFibrancyGenerators.{u}
  let A : T.toSet ⊕ T.toSet → ResolutionDiagram.{u} :=
    Sum.elim (fun r ↦ r.1.left) (fun r ↦ r.1.right)
  let h := DaggerSmithSolutionSet.uniformPresentability A
  exact ⟨h.choose, h.choose_spec.choose, fun r ↦ h.choose_spec.choose_spec (.inl r),
    fun r ↦ h.choose_spec.choose_spec (.inr r)⟩

local instance localGeneratorRankRegular : Fact localGeneratorRank.{u}.κ.IsRegular :=
  ⟨localGeneratorRank.regular⟩

local instance localGeneratorRankOrderBot : OrderBot localGeneratorRank.{u}.κ.ord.ToType :=
  Cardinal.toTypeOrderBot localGeneratorRank.regular.ne_zero

local instance localGeneratorRankSuitable :
    resolutionLocalFibrancyGenerators.{u}.IsCardinalForSmallObjectArgument localGeneratorRank.{u}.κ where
  preservesColimit := by
    intro A B X Y i hi f hf
    let r : resolutionLocalFibrancyGenerators.{u}.toSet := ⟨Arrow.mk i, hi⟩
    letI : IsCardinalPresentable A localGeneratorRank.{u}.κ := localGeneratorRank.left r
    have := preservesColimitsOfShape_of_isCardinalPresentable A localGeneratorRank.{u}.κ
      localGeneratorRank.{u}.κ.ord.ToType
    infer_instance

private def localFibrantFactorization :
    FunctorialFactorizationData resolutionLocalFibrancyGenerators.{u}.rlp.llp
      resolutionLocalFibrancyGenerators.{u}.rlp :=
  SmallObject.functorialFactorizationData resolutionLocalFibrancyGenerators localGeneratorRank.κ

/-- Small object replacement by the Reedy trivial generators and the vertex boxes. -/
def resolutionLocalFibrantReplacement : ResolutionDiagram.{u} ⥤ ResolutionDiagram.{u} :=
  resolutionTerminalArrow ⋙ localFibrantFactorization.Z

/-- The natural unit of the small object replacement. -/
def resolutionLocalFibrantReplacementUnit :
    𝟭 ResolutionDiagram.{u} ⟶ resolutionLocalFibrantReplacement :=
  Functor.whiskerLeft resolutionTerminalArrow localFibrantFactorization.i

theorem resolutionLocalFibrantReplacement_isLocal (W : ResolutionDiagram.{u}) :
    resolutionLocalObject (resolutionLocalFibrantReplacement.obj W) := by
  apply (resolutionLocalObject_iff_rlp _).mpr
  have h := localFibrantFactorization.hp (resolutionTerminalArrow.obj W)
  convert h using 1
  apply terminal.hom_ext

theorem resolutionLocalFibrantReplacementUnit_llp (W : ResolutionDiagram.{u}) :
    resolutionLocalFibrancyGenerators.rlp.llp (resolutionLocalFibrantReplacementUnit.app W) :=
  localFibrantFactorization.hi (resolutionTerminalArrow.obj W)

theorem resolutionLocalFibrantReplacementUnit_cofibration (W : ResolutionDiagram.{u}) :
    reedyCofibrations (resolutionLocalFibrantReplacementUnit.app W) := by
  have h : resolutionLocalFibrancyGenerators.{u} ≤ cofibrations ResolutionDiagram.{u} :=
    resolutionLocalFibrancyGenerators_le.trans inf_le_left
  have hh := antitone_llp (antitone_rlp h)
  rw [rlp_eq_of_wfs (cofibrations ResolutionDiagram.{u}) (trivialFibrations ResolutionDiagram.{u}),
    llp_eq_of_wfs (cofibrations ResolutionDiagram.{u}) (trivialFibrations ResolutionDiagram.{u})] at hh
  exact hh _ (resolutionLocalFibrantReplacementUnit_llp W)

private theorem resolutionTerminalArrow_accessible :
    resolutionTerminalArrow.{u}.IsCardinalAccessible localGeneratorRank.{u}.κ := by
  constructor
  intro J _ _
  letI := isFiltered_of_isCardinalFiltered J localGeneratorRank.{u}.κ
  letI := IsFiltered.isConnected J
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨isColimitArrowOfComponents _ ?_ ?_⟩
  · exact hc
  · exact isColimitConstCocone J (⊤_ ResolutionDiagram.{u})

/-- The particular small object replacement is accessible. -/
theorem resolutionLocalFibrantReplacement_accessible :
    Functor.IsAccessible.{u} resolutionLocalFibrantReplacement.{u} := by
  letI := resolutionDiagramLocallyPresentable.{u}
  let κ := localGeneratorRank.{u}.κ
  let T := resolutionLocalFibrancyGenerators.{u}
  letI : ∀ r : T.toSet, IsCardinalPresentable r.1.left κ := localGeneratorRank.left
  letI : ∀ r : T.toSet, IsCardinalPresentable r.1.right κ := localGeneratorRank.right
  letI : (DaggerSOAAccessible.rightFactor localFibrantFactorization.{u}).IsCardinalAccessible κ :=
    DaggerSOAStepAccessible.property_rightFactor_accessible T κ
  letI := resolutionTerminalArrow_accessible
  letI : (Arrow.leftFunc : Arrow ResolutionDiagram.{u} ⥤ ResolutionDiagram.{u}).IsCardinalAccessible κ :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  change Functor.IsAccessible.{u}
    (resolutionTerminalArrow ⋙ DaggerSOAAccessible.rightFactor localFibrantFactorization ⋙ Arrow.leftFunc)
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

/-- The small object replacement unit is a local equivalence. -/
theorem resolutionLocalFibrantReplacementUnit_local (W : ResolutionDiagram.{u}) :
    resolutionLocalEquivalences (resolutionLocalFibrantReplacementUnit.app W) := by
  let T := resolutionLocalFibrancyGenerators.{u}
  let P := reedyCofibrations.{u} ⊓ resolutionLocalEquivalences
  letI := resolutionSmallObjectArgument T
  have hT : T ≤ P := resolutionLocalFibrancyGenerators_le
  have hcell : (coproducts.{u} T).pushouts ≤ P :=
    (DaggerCoproductCellSerialization.coproduct_pushouts_le T).trans
      ((transfiniteCompositions_monotone ((pushouts_monotone hT).trans P.pushouts_le)).trans
        P.transfiniteCompositions_le)
  have h := resolutionLocalFibrantReplacementUnit_llp W
  change T.rlp.llp _ at h
  rw [T.llp_rlp_of_hasSmallObjectArgument] at h
  letI : P.IsStableUnderRetracts := by
    constructor
    intro A B f X Y g r h
    exact ⟨(cofibrations ResolutionDiagram.{u}).of_retract r h.1,
      resolutionLocalEquivalences.of_retract r h.2⟩
  have h' : P _ := P.retracts_le _
    (retracts_monotone ((transfiniteCompositions_monotone hcell).trans P.transfiniteCompositions_le) _ h)
  exact h'.2

/-- A local unit makes the local weak class the inverse image of dagger Joyal
weak equivalences under replacement followed by evaluation at zero. -/
theorem resolutionLocalEquivalences_eq_inverseImage_of_localUnit
    (hη : ∀ W : ResolutionDiagram.{u},
      resolutionLocalEquivalences (resolutionLocalFibrantReplacementUnit.app W)) :
    resolutionLocalEquivalences.{u} =
      (weakEquivalences DaggerSSet.{u}).inverseImage
        (resolutionLocalFibrantReplacement ⋙ evaluationAt 0) := by
  ext W V f
  let L := resolutionLocalFibrantReplacement.{u}
  exact (resolutionLocalEquivalences_iff_of_localReplacement L
    resolutionLocalFibrantReplacementUnit resolutionLocalFibrantReplacement_isLocal hη f).trans
    (reedyWeakEquivalence_iff_evalZero_of_homotopicallyConstant (L.map f)
      ((resolutionLocalObject_iff_homotopicallyConstant _).mp
        (resolutionLocalFibrantReplacement_isLocal W)).2
      ((resolutionLocalObject_iff_homotopicallyConstant _).mp
        (resolutionLocalFibrantReplacement_isLocal V)).2)

/-- The local weak class is computed by the replacement followed by zero evaluation. -/
theorem resolutionLocalEquivalences_eq_inverseImage :
    resolutionLocalEquivalences.{u} =
      (weakEquivalences DaggerSSet.{u}).inverseImage
        (resolutionLocalFibrantReplacement ⋙ evaluationAt 0) :=
  resolutionLocalEquivalences_eq_inverseImage_of_localUnit resolutionLocalFibrantReplacementUnit_local

end

end DaggerModels.PartII
