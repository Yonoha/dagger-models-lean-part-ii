import DaggerModelsPartII.JTSupportedNormalizationComparison
import DaggerModelsPartII.TotalElementsWeakComparison

/-! The actual joint index reverses both the coefficient and time operators. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphCommonCenter

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTRowGraphFiber JTRowGraphNormalizationDiagram JTMixedGraphEndpointLifts

noncomputable section

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev originalNorm :=
  (supportAt q).op ⋙ JTRowGraphNormalizationDiagram.diagram hx hy

/-- The joint index uses the opposite of the category of elements of
the whole presheaf, so both graph and time operators point forward. -/
abbrev JointChoiceIndex :=
  (GrothendieckTotalElements.totalDiagram (pairedDegreeDiagram q hx hy)).Elementsᵒᵖ

private def jointForget :
    GrothendieckTotalElements.elementDiagram (pairedDegreeDiagram q hx hy) ⟶
      originalNorm hx hy ⋙ Functor.elementsFunctor :=
  Functor.whiskerRight (pairedDegreeForget q hx hy) Functor.elementsFunctor ≫
    Functor.whiskerLeft (originalNorm hx hy) JTSemiSimplexElementsWeak.elementForgetUnopNat

private theorem point_op_iff (D : Type) [SmallCategory D] :
    GW (pointMap (nerve Dᵒᵖ)) ↔ GW (pointMap (nerve D)) := by
  let e := DaggerNativeNerveOppositeIso.nerveOppositeIso D
  letI : SSet.opFunctor.{0}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let i := (IsTerminal.isTerminalObj SSet.opFunctor.{0} _ pointIsTerminal).uniqueUpToIso
    pointIsTerminal
  have he : e.inv ≫ SSet.opFunctor.map (pointMap (nerve D)) ≫ i.hom =
      pointMap (nerve Dᵒᵖ) := pointIsTerminal.hom_ext _ _
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, ← he]
  rw [weakEquivalence_precomp_iff e.inv, weakEquivalence_postcomp_iff _ i.hom]
  exact DaggerNativeSimplicialOppositeKanWeak.weak_op_iff _

/-- The actual joint index is weakly contractible when the exact forgetful
component on every coefficient has weak nerve. -/
theorem jointChoiceIndex_point_GW_of_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (h : ∀ G : (Fiber q)ᵒᵖ, WeakEquivalence
      (nerveMap ((supportedForgetComparison hx hy).app G).toFunctor)) :
    GW (pointMap (nerve (JointChoiceIndex hx hy))) := by
  let A := pairedDegreeDiagram q hx hy
  let B := originalNorm hx hy ⋙ Functor.elementsFunctor
  let β := jointForget hx hy
  have hB (G : (Fiber q)ᵒᵖ) : GW (pointMap (nerve (B.obj G))) :=
    (point_op_iff (B.obj G)).mp (supportedTargetElements_point_GW hx hy G.unop hW)
  letI : WeakEquivalence (nerveMap (Grothendieck.forget B)) :=
    GrothendieckContractibleFibers.projection_weak B hB
  letI : WeakEquivalence (pointMap (nerve (Fiber q)ᵒᵖ)) :=
    (weakEquivalence_iff_GW _).mpr ((point_op_iff (Fiber q)).mpr (JTRowGraphFiber.point_GW q))
  have ht : nerveMap (Grothendieck.forget B) ≫ pointMap (nerve (Fiber q)ᵒᵖ) =
      pointMap (nerve (Grothendieck B)) := pointIsTerminal.hom_ext _ _
  letI : WeakEquivalence (pointMap (nerve (Grothendieck B))) := by rw [← ht]; infer_instance
  have hβ (G : (Fiber q)ᵒᵖ) : WeakEquivalence (nerveMap (β.app G).toFunctor) :=
    (TotalElementsWeakComparison.nerveMap_op_iff _).mp (h G)
  letI : WeakEquivalence (nerveMap (Grothendieck.map β)) := GrothendieckNerveMapWeak.map_weak β hβ
  have hs : nerveMap (Grothendieck.map β) ≫ pointMap (nerve (Grothendieck B)) =
      pointMap (nerve (Grothendieck (GrothendieckTotalElements.elementDiagram A))) :=
    pointIsTerminal.hom_ext _ _
  letI : WeakEquivalence
      (pointMap (nerve (Grothendieck (GrothendieckTotalElements.elementDiagram A)))) := by
    rw [← hs]
    infer_instance
  let e := (GrothendieckTotalElements.equivalence A).functor
  letI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  have he : nerveMap e ≫ pointMap (nerve (GrothendieckTotalElements.totalDiagram A).Elements) =
      pointMap (nerve (Grothendieck (GrothendieckTotalElements.elementDiagram A))) :=
    pointIsTerminal.hom_ext _ _
  apply (point_op_iff _).mpr
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  rw [he]
  infer_instance

end
end DaggerModels.PartII.JTRowGraphCommonCenter
