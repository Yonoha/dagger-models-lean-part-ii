import DaggerModelsPartII.ReedyBoundaryLifting
import DaggerModelsPartII.ReedyModelComparison
import DaggerModelsPartII.ResolutionPresentable

/-! Small generating families for the exact Reedy model structure of Part II. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe u

namespace DaggerModels.PartII

noncomputable section

local instance reedyGeneratorCoefficientLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance reedyGeneratorCoefficientColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance reedyGeneratorCoefficientModel : ModelCategory DaggerSSet.{u} := DaggerOriginalJoyalModel.standardModelCategory
local instance reedyGeneratorModel : ModelCategory ResolutionDiagram.{u} := resolutionReedyModelCategory

private def reedyBoundaryGenerator (T : MorphismProperty DaggerSSet.{u}) (g : ℕ × T.toSet) :
    Arrow ResolutionDiagram.{u} :=
  Arrow.mk (reedyBoundaryBox g.1 g.2.1.hom)

/-- The boundary pushout-products of all maps in a coefficient family. -/
def reedyBoundaryGenerators (T : MorphismProperty DaggerSSet.{u}) :
    MorphismProperty ResolutionDiagram.{u} :=
  ofHoms (fun g : ℕ × T.toSet ↦ (reedyBoundaryGenerator T g).hom)

instance (T : MorphismProperty DaggerSSet.{u}) [IsSmall.{u} T] :
    IsSmall.{u} (reedyBoundaryGenerators T) :=
  isSmall_ofHoms _

private theorem reedyBoundaryGenerator_mem (T : MorphismProperty DaggerSSet.{u})
    (g : ℕ × T.toSet) : reedyBoundaryGenerators T (reedyBoundaryGenerator T g).hom :=
  ⟨g⟩

/-- Testing against the boundary pushout-products tests each relative matching map. -/
theorem reedyBoundaryGenerators_rlp (T : MorphismProperty DaggerSSet.{u}) :
    (reedyBoundaryGenerators T).rlp = reedyMatchingProperty T.rlp := by
  ext X Y f
  constructor
  · intro h n A B i hi
    let g : ℕ × T.toSet := (n, ⟨Arrow.mk i, (T.arrow_mk_mem_toSet_iff i).mpr hi⟩)
    have hgen := h (reedyBoundaryGenerator T g).hom (reedyBoundaryGenerator_mem T g)
    exact (reedyBoundaryBox_hasLiftingProperty_iff n i f).mp hgen
  · intro h A B g hg
    change (ofHoms (fun k : ℕ × T.toSet ↦ (reedyBoundaryGenerator T k).hom)) g at hg
    obtain ⟨k⟩ := hg
    exact (reedyBoundaryBox_hasLiftingProperty_iff k.1 k.2.1.hom f).mpr
      (h k.1 k.2.1.hom k.2.property)

/-- The Reedy generating cofibrations use the literal Part I free boundaries. -/
def resolutionReedyI : MorphismProperty ResolutionDiagram.{u} :=
  reedyBoundaryGenerators DaggerActualWeakAccessibility.originalID.{u}

/-- The Reedy generating trivial cofibrations use the actual Part I Smith family. -/
def resolutionReedyJ : MorphismProperty ResolutionDiagram.{u} :=
  reedyBoundaryGenerators (DaggerOriginalJoyalModel.generatedJ
    DaggerUnitaryInvariance.standardReplacement.{u})

instance resolutionReedyI_small : IsSmall.{u} resolutionReedyI.{u} := by
  letI := DaggerOriginalJoyalModel.standardCombinatorialData.{u}.smallI
  exact inferInstanceAs (IsSmall.{u} (reedyBoundaryGenerators
    DaggerActualWeakAccessibility.originalID.{u}))

instance resolutionReedyJ_small : IsSmall.{u} resolutionReedyJ.{u} := by
  letI := DaggerOriginalJoyalModel.generatedJ_small DaggerUnitaryInvariance.standardReplacement.{u}
  exact inferInstanceAs (IsSmall.{u} (reedyBoundaryGenerators
    (DaggerOriginalJoyalModel.generatedJ DaggerUnitaryInvariance.standardReplacement.{u})))

theorem resolutionReedyI_rlp :
    resolutionReedyI.{u}.rlp = trivialFibrations ResolutionDiagram.{u} := by
  have h : trivialFibrations DaggerSSet.{u} = DaggerActualWeakAccessibility.originalID.{u}.rlp :=
    DaggerOriginalJoyalModel.model_trivialFibrations DaggerUnitaryInvariance.standardReplacement
  change (reedyBoundaryGenerators DaggerActualWeakAccessibility.originalID.{u}).rlp =
    reedyFibrations ⊓ reedyWeakEquivalences
  rw [reedyBoundaryGenerators_rlp, ← h, reedyFibrations_inf_weakEquivalences]
  rfl

theorem resolutionReedyJ_rlp :
    resolutionReedyJ.{u}.rlp = fibrations ResolutionDiagram.{u} := by
  let D := DaggerOriginalJoyalModel.standardCombinatorialData.{u}
  have h : (DaggerOriginalJoyalModel.generatedJ
      DaggerUnitaryInvariance.standardReplacement.{u}).rlp = fibrations DaggerSSet.{u} :=
    D.fibrations.trans D.modelFib.symm
  change (reedyBoundaryGenerators (DaggerOriginalJoyalModel.generatedJ
    DaggerUnitaryInvariance.standardReplacement.{u})).rlp = reedyFibrations
  rw [reedyBoundaryGenerators_rlp, h]
  rfl

/-- Small families in the resolution category admit the small object argument. -/
theorem resolutionSmallObjectArgument (T : MorphismProperty ResolutionDiagram.{u})
    [IsSmall.{u} T] : HasSmallObjectArgument.{u} T := by
  letI := resolutionDiagramLocallyPresentable.{u}
  exact DaggerSmithSolutionSet.smallObjectArgument T

/-- Part II, `cs.lem.reedy`: local presentability and both small generating families. -/
theorem resolutionReedy_combinatorial :
    IsLocallyPresentable.{u} ResolutionDiagram.{u} ∧
      ∃ I J : MorphismProperty ResolutionDiagram.{u},
        IsSmall.{u} I ∧ IsSmall.{u} J ∧
          HasSmallObjectArgument.{u} I ∧ HasSmallObjectArgument.{u} J ∧
          I.rlp = trivialFibrations ResolutionDiagram.{u} ∧
          J.rlp = fibrations ResolutionDiagram.{u} :=
  ⟨resolutionDiagramLocallyPresentable, resolutionReedyI, resolutionReedyJ,
    resolutionReedyI_small, resolutionReedyJ_small,
    resolutionSmallObjectArgument _, resolutionSmallObjectArgument _,
    resolutionReedyI_rlp, resolutionReedyJ_rlp⟩

end

end DaggerModels.PartII
