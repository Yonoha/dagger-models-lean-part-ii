import DaggerModelsPartII.SemiSimplexBoundaryComparison
import DaggerModelsPartII.JTSupportedNormalizationJointComparison

/-! The joint index of actual supported common-coefficient choices is weakly contractible. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphCommonCenter

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTRowGraphFiber JTMixedGraphEndpointLifts
open SemiSimplexBoundaryLifting

private noncomputable abbrev rawVertex :=
  JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)
variable (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
include hW

/-- Every actual forgetful component has weak nerve by its paired full
relative boundary lifting. -/
theorem supportedForgetComparison_weak (G : (Fiber q)ᵒᵖ) :
    WeakEquivalence (nerveMap ((supportedForgetComparison hx hy).app G).toFunctor) := by
  change WeakEquivalence
    (nerveMap ((supportedForgetComparison hx hy).app (op G.unop)).toFunctor)
  rw [supportedForgetComparison_app hx hy G.unop]
  exact (weakEquivalence_iff_GW _).mpr
    (toFullElements_weak (pairedDegreeForget_boundaryLifting hx hy hW G.unop))

/-- The same joint coefficient/time index used by the decorated evaluation
has weakly contractible nerve for each supported raw simplex. -/
theorem jointChoiceIndex_point_GW : GW (pointMap (nerve (JointChoiceIndex hx hy))) :=
  jointChoiceIndex_point_GW_of_weak hx hy hW (supportedForgetComparison_weak hx hy hW)

end DaggerModels.PartII.JTRowGraphCommonCenter
