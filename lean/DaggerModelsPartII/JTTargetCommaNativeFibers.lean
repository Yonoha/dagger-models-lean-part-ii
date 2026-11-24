import DaggerModelsPartII.JTNativePresentationFibers
import DaggerModelsPartII.JTNativeFiberElements
import DaggerModelsPartII.FiberedNerveCriterion
import DaggerModelsPartII.JTRezkRecognition
import DaggerModelsPartII.JTGraphFactoredPresentation

/-! Reduce the exact fixed-target comma to strict fibers over its native slice. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTTargetCommaNativeFibers

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTTargetCommaPullback (diagram equivalence snd map_snd)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private def targetProjection : diagram W x y Q ⟶
    (Functor.const _).obj (necklaceUnder.obj Q.code) where
  app := snd W x y Q
  naturality {_ _} f := (map_snd W x y Q f).trans (Category.comp_id _).symm

/-- The exact pullback presentation over the slice of the original native target. -/
def projection : JTTargetCommaPullback.Presentation W x y Q ⥤ Over Q.code :=
  JTNativePresentationFibers.projection (diagram W x y Q) (targetProjection Q)

/-- All complete decorated lifts of the given map over the same native target. -/
abbrev lifts (P : Over Q.code) :=
  JTNativeFiberElements.lifts (diagram W x y Q) (targetProjection Q) P

/-- In the strict fiber, the remaining operators act on the decorated labels. -/
def liftEquivalence (P : Over Q.code) :
    (lifts Q P).Elements ≌ Functor.Fiber (projection Q) P :=
  JTNativeFiberElements.equivalence (diagram W x y Q) (targetProjection Q) P

private theorem comma_point (h : ∀ P : Over Q.code,
    GW (pointMap (nerve (Functor.Fiber (projection Q) P)))) :
    GW (pointMap (nerve (TargetComma Q))) := by
  haveI : (projection Q).IsFibered :=
    JTNativePresentationFibers.isFibered (targetProjection Q)
  let f := nerveMap (equivalence W x y Q).functor
  let p := nerveMap (projection Q)
  let t := pointMap (nerve (Over Q.code))
  haveI : WeakEquivalence f :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  haveI : WeakEquivalence p := FiberedNerveCriterion.projection_weak (projection Q) h
  haveI : WeakEquivalence t := (weakEquivalence_iff_GW _).mpr
    (DaggerNativeOverNerveWeakContractibility.point_GW Q.code)
  have ht : f ≫ p ≫ t = pointMap (nerve (TargetComma Q)) := pointIsTerminal.hom_ext _ _
  rw [← ht, ← weakEquivalence_iff_GW]
  infer_instance

/-- Weak contractibility of all the strict fibers over the exact native
target maps suffices for the original four-link Theorem C. -/
theorem theoremC_of_native_fibers
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (P : Over Q.code), GW (pointMap (nerve (Functor.Fiber (projection Q) P)))) :
    TheoremCStatement.statement :=
  JTRezkRecognition.theoremC_of_targetCommas fun W hW x y Q ↦ comma_point Q (h W hW x y Q)

/-- The same criterion stated as contractibility of the categories of exact decorated lifts. -/
theorem theoremC_of_native_lifts
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (P : Over Q.code), GW (pointMap (nerve (lifts Q P).Elements))) :
    TheoremCStatement.statement := by
  apply theoremC_of_native_fibers
  intro W hW x y Q P
  let f := nerveMap (liftEquivalence Q P).functor
  let t := pointMap (nerve (Functor.Fiber (projection Q) P))
  haveI : WeakEquivalence f :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have ht : f ≫ t = pointMap (nerve (lifts Q P).Elements) := pointIsTerminal.hom_ext _ _
  haveI : WeakEquivalence (f ≫ t) := (weakEquivalence_iff_GW _).mpr (ht.symm ▸ h W hW x y Q P)
  exact (weakEquivalence_iff_GW _).mp (weakEquivalence_of_precomp f t)

end
end DaggerModels.PartII.JTTargetCommaNativeFibers
