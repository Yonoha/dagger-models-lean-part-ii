import DaggerModelsPartII.JTSupportedNormalizationDiagrams
import DaggerModelsPartII.JTSupportedNormalizationTarget
import DaggerModelsPartII.JTSemiSimplexElementsWeak
import DaggerModelsPartII.GrothendieckNerveMapWeak

/-! The natural comparison of the chosen enlarged normalization diagrams to
the original full categories of normalization simplices. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphCommonCenter

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTRowGraphFiber JTRowGraphNormalizationDiagram JTMixedGraphEndpointLifts
open SemiSimplexBoundaryLifting

noncomputable section

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

/-- The actual enlarged choices and all original mixed operators. -/
def supportedSourceDiagram : (Fiber q)ᵒᵖ ⥤ Cat.{0,0} :=
  pairedDegreeDiagram q hx hy ⋙ Functor.elementsFunctor ⋙ Cat.opFunctor

/-- Apply the actual mixed forgetful map, then include the injective time
operators into the original full simplex category. -/
def supportedForgetComparison :
    supportedSourceDiagram hx hy ⟶ supportedTargetDiagram hx hy :=
  Functor.whiskerRight (pairedDegreeForget q hx hy)
      (Functor.elementsFunctor ⋙ Cat.opFunctor) ≫
    Functor.whiskerLeft ((supportAt q).op ⋙ JTRowGraphNormalizationDiagram.diagram hx hy)
      JTSemiSimplexElementsWeak.elementForgetNat

/-- The component of the natural comparison is the actual forgetful functor
between categories of elements. It preserves original target operators. -/
theorem supportedForgetComparison_app (G : Fiber q) :
    ((supportedForgetComparison hx hy).app (op G)).toFunctor =
      (NatTrans.mapElements ((pairedDegreeForget q hx hy).app (op G))).op ⋙
        JTSemiSimplexElementsWeak.elementForget
          ((JTRowGraphNormalizationDiagram.diagram hx hy).obj (op ((supportAt q).obj G))) := rfl

/-- The component of the mixed normalized forgetful transformation has the
same relative boundary lifting as the fixed-graph map. -/
theorem pairedDegreeForget_boundaryLifting
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (G : Fiber q) : HasBoundaryLifting ((pairedDegreeForget q hx hy).app (op G)) := by
  rw [pairedDegreeForget_app]
  exact (pairedNormalization_boundaryLifting q hx hy G hW).precompIso (pairedFixedIso q hx hy G)

/-- A fiberwise Kan weak comparison contracts the whole enlarged diagram
through the original full normalization simplex categories. -/
theorem supportedSourceTotal_point_GW_of_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (h : ∀ G : (Fiber q)ᵒᵖ, WeakEquivalence
      (nerveMap ((supportedForgetComparison hx hy).app G).toFunctor)) :
    GW (pointMap (nerve (Grothendieck (supportedSourceDiagram hx hy)))) := by
  let α := supportedForgetComparison hx hy
  letI : WeakEquivalence (nerveMap (Grothendieck.map α)) := GrothendieckNerveMapWeak.map_weak α h
  letI : WeakEquivalence (pointMap (nerve (Grothendieck (supportedTargetDiagram hx hy)))) :=
    (weakEquivalence_iff_GW _).mpr (supportedTargetTotal_point_GW hx hy hW)
  have he : nerveMap (Grothendieck.map α) ≫
        pointMap (nerve (Grothendieck (supportedTargetDiagram hx hy))) =
      pointMap (nerve (Grothendieck (supportedSourceDiagram hx hy))) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerModels.PartII.JTRowGraphCommonCenter
