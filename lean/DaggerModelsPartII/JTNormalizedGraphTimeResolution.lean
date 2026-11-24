import DaggerModelsPartII.JTHomotopyTargetTimeResolution
import DaggerModelsPartII.JTHigherGraphExtensionTrivialFibration
import DaggerModelsPartII.JTNormalizedGraphTargetArrow

/-! Weakly contractible sources of the higher comparisons over a fixed graph. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTNormalizedGraphTimeResolution

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTRowGraphFiber JTRowGraphNormalizationDiagram JTMixedGraphEndpointLifts
open JTHigherGraphExtensionComma JTHigherGraphExtensionTrivialFibration
open JTHomotopyTargetTimeResolution JTMixedGraphRawRefinement

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)
variable (G : Fiber q)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy

/-- The exact paired interleaved extensions over the given graph. -/
abbrev Extensions := choices (coefficient G) G.obj.parameter
  (leftEndpoint hx G) (rightEndpoint hy G)

/-- The paired interleaved extensions have weakly contractible time space. -/
theorem extensions_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (Extensions hx hy G)) := by
  letI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  let p := forgetChoices (coefficient G) G.obj.parameter (leftEndpoint hx G) (rightEndpoint hy G)
  haveI : WeakEquivalence p :=
    ((mem_trivialFibrations_iff _).mp
      (forgetChoices_trivialFibration (coefficient G) G.obj.parameter
        (leftEndpoint hx G) (rightEndpoint hy G))).2
  let t := SSet.stdSimplex.isTerminalObj₀.from ((diagram hx hy).obj (op G))
  haveI : WeakEquivalence t := point_at_weak hx hy hW G
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  have h : p ≫ t ≫ e.hom = pointMap (Extensions hx hy G) := pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- All internal necklaces in every time cylinder over the graph. -/
abbrev Resolution := TimeResolution (MixedGraphCylinderTraversal.code d) (Extensions hx hy G)

/-- This full time resolution has weakly contractible nerve. -/
theorem resolution_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (Resolution hx hy G))) :=
  (point_GW_iff _ _).mpr (extensions_point_GW hx hy G hW)

/-- The time resolution maps into the original fixed-target comma, with the
original graph realization and both ordered endpoints. -/
def toComma : Resolution hx hy G ⥤
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) (Q hx hy) :=
  JTHigherGraphExtensionComma.toComma (coefficient G) G.obj.parameter
    (leftEndpoint hx G) (rightEndpoint hy G)
    (congrArg (fun a ↦ (singleIso d).hom ≫ a) (raw_eq G)) (Q hx hy).first (Q hx hy).last

/-- For the original single-bead target, proving that this comparison is weak
is equivalent to proving weak contractibility of the full fixed-target comma. -/
theorem toComma_weak_iff
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toComma hx hy G)) ↔
      GW (pointMap (nerve
        (CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) (Q hx hy)))) := by
  let f := nerveMap (toComma hx hy G)
  let t := pointMap (nerve
    (CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) (Q hx hy)))
  have h : f ≫ t = pointMap (nerve (Resolution hx hy G)) := pointIsTerminal.hom_ext _ _
  haveI : WeakEquivalence (f ≫ t) :=
    (weakEquivalence_iff_GW _).mpr (h.symm ▸ resolution_point_GW hx hy G hW)
  change WeakEquivalence f ↔ GW t
  rw [← weakEquivalence_iff_GW]
  constructor
  · intro hf
    letI : WeakEquivalence f := hf
    exact (weakEquivalence_precomp_iff f t).mp inferInstance
  · intro ht
    letI : WeakEquivalence t := ht
    exact (weakEquivalence_postcomp_iff f t).mp inferInstance

end

end DaggerModels.PartII.JTNormalizedGraphTimeResolution
