import DaggerModelsPartII.JTRowGraphNormalizationDiagram
import DaggerModelsPartII.OrderedLabelNaturalWeakSpans
import DaggerModelsPartII.GrothendieckContractibleFibers

/-! The original opposite category of normalization simplices at a supported graph. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphCommonCenter

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTRowGraphFiber JTRowGraphNormalizationDiagram JTMixedGraphEndpointLifts

private noncomputable abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The actual product normalization target has weakly contractible opposite
category of elements, by the checked simplicial resolution span. -/
theorem supportedTargetElements_point_GW {W : SegalLocalizers.ReverseDaggerSpace.{0}}
    {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
    (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)
    (G : Fiber q)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap
      (nerve ((JTRowGraphNormalizationDiagram.diagram hx hy).obj
        (op ((supportAt q).obj G))).Elementsᵒᵖ)) := by
  let H := (supportAt q).obj G
  let X := (JTRowGraphNormalizationDiagram.diagram hx hy).obj (op H)
  let p := SSet.stdSimplex.isTerminalObj₀.from X
  letI : WeakEquivalence p := point_at_weak hx hy hW H
  let i := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  haveI : WeakEquivalence (pointMap X) := by
    rw [← pointIsTerminal.hom_ext (p ≫ i.hom) (pointMap X)]
    infer_instance
  let a := SimplicialResolutionFunctor.augmentation.app X
  let e := SimplicialResolutionFunctor.elementsProjection.app X
  letI : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak X
  letI : WeakEquivalence e := SimplicialResolutionFunctor.elementsProjection_weak X
  apply (weakEquivalence_iff_GW _).mp
  change WeakEquivalence (pointMap (nerve X.Elementsᵒᵖ))
  apply (weakEquivalence_precomp_iff e _).mp
  rw [pointIsTerminal.hom_ext (e ≫ pointMap (nerve X.Elementsᵒᵖ)) (a ≫ pointMap X)]
  infer_instance

noncomputable section

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

/-- The exact target category at every supported graph, with full simplex operators. -/
def supportedTargetDiagram : (Fiber q)ᵒᵖ ⥤ Cat.{0,0} :=
  (supportAt q).op ⋙ JTRowGraphNormalizationDiagram.diagram hx hy ⋙
    SimplicialResolutionFunctor.elementsOpposite

/-- The full original normalization diagram over the supported graphs
has weakly contractible total nerve. -/
theorem supportedTargetTotal_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (Grothendieck (supportedTargetDiagram hx hy)))) := by
  let F := supportedTargetDiagram hx hy
  haveI : WeakEquivalence (nerveMap (Grothendieck.forget F)) :=
    GrothendieckContractibleFibers.projection_weak F
      (fun G ↦ supportedTargetElements_point_GW hx hy G.unop hW)
  haveI : WeakEquivalence (pointMap (nerve (Fiber q))) :=
    (weakEquivalence_iff_GW _).mpr (JTRowGraphFiber.point_GW q)
  haveI := DaggerNativeSimplicialOppositeKanWeak.op_weak (pointMap (nerve (Fiber q)))
  let e := DaggerNativeNerveOppositeIso.nerveOppositeIso (Fiber q)
  letI : SSet.opFunctor.{0}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let ht := IsTerminal.isTerminalObj SSet.opFunctor.{0} _ pointIsTerminal
  let e' := ht.uniqueUpToIso pointIsTerminal
  have he : e.inv ≫ SSet.opFunctor.map (pointMap (nerve (Fiber q))) ≫ e'.hom =
      pointMap (nerve (Fiber q)ᵒᵖ) := pointIsTerminal.hom_ext _ _
  haveI : WeakEquivalence (pointMap (nerve (Fiber q)ᵒᵖ)) := by
    rw [← he]
    infer_instance
  have h : nerveMap (Grothendieck.forget F) ≫ pointMap (nerve (Fiber q)ᵒᵖ) =
      pointMap (nerve (Grothendieck F)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  change WeakEquivalence (pointMap (nerve (Grothendieck F)))
  rw [← h]
  infer_instance

end
end DaggerModels.PartII.JTRowGraphCommonCenter
