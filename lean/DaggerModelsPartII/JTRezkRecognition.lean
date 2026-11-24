import DaggerModelsPartII.DiagonalRecognition
import DaggerModelsPartII.JTRelativeRowWeak
import DaggerModelsPartII.JTWalkingDiagonalTransfer
import DaggerModelsPartII.JTStrictificationInjectiveComparison
import DaggerModelsPartII.JTRawChosenFiberBridge
import DaggerModelsPartII.JTTheoremCFromStrictification
import DaggerModelsPartII.JTTargetCommaPullbackBar

/-! The original ordered mapping-space criterion for complete reversal
Segal diagrams, and its application to the chosen JT comparison. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialPiZeroWeakEquivalence
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRezkRecognition

open SegalLocalizers JTUnitaryDiagonalPath JTProjectiveOrderedFiberComparison
open ChosenHomotopyFiberFunctor JTFirstRowWeakRecognition

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ
private abbrev K := (Δ[0] : SSet.{0})

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

private theorem zero_fibrant (W : S) [IsFibrant W] : IsFibrant (Zero W) := by
  let e := OrderedSimplexEndpointFiber.freeMappingIso W 0
  letI := JTRelativeRowWeak.row_fibrant W (op ⟨0⟩)
  exact (isFibrant_iff_of_isTerminal (e.hom ≫ terminal.from _) terminalIsTerminal).mpr
    inferInstance

private theorem zero_natural {W Z : S} (f : W ⟶ Z) :
    diagramMappingPostcomp (daggerSimplex 0) f ≫
      (OrderedSimplexEndpointFiber.freeMappingIso Z 0).hom =
      (OrderedSimplexEndpointFiber.freeMappingIso W 0).hom ≫ f.app (op ⟨0⟩) := by
  apply NatTrans.ext
  funext q η
  rfl

private theorem zero_components_surjective {W Z : S} (f : W ⟶ Z)
    (hπ : Function.Surjective (SSet.mapπ₀ (rowMap f ⦋0⦌))) :
    Function.Surjective (SSet.mapπ₀ (diagramMappingPostcomp (daggerSimplex 0) f)) := by
  let eW := OrderedSimplexEndpointFiber.freeSimplexRowIso W 0
  let eZ := OrderedSimplexEndpointFiber.freeSimplexRowIso Z 0
  let m := diagramMappingPostcomp (daggerSimplex 0) f
  have hn : m ≫ eZ.hom = eW.hom ≫ rowMap f ⦋0⦌ := by
    apply NatTrans.ext
    funext q η
    rfl
  intro y
  obtain ⟨x, hx⟩ := hπ (SSet.mapπ₀ eZ.hom y)
  obtain ⟨a, ha⟩ := (bijective_mapPiZero eW.hom).2 x
  refine ⟨a, (bijective_mapPiZero eZ.hom).1 ?_⟩
  rw [← SSet.mapπ₀_comp_apply, hn, SSet.mapπ₀_comp_apply, ha, hx]

/-- Between the original injectively fibrant, unitarily complete Segal
diagrams, weakness on all ordered mapping spaces and surjectivity on
zero-row components imply rowwise weakness. -/
theorem weak_of_ordered_fibers_and_components
    {W Z : S} [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z)
    (hW : unitarilyCompleteSegalCondition W) (hZ : unitarilyCompleteSegalCondition Z)
    (hπ : Function.Surjective (SSet.mapπ₀ (rowMap f ⦋0⦌)))
    (hf : ∀ x y : (row W ⦋0⦌).obj (op ⦋0⦌), WeakEquivalence
      (JTInjectiveOrderedFiberTransfer.strictFiberMap f x y)) : WeakEquivalence f := by
  letI := JTRelativeRowWeak.row_fibrant W (op ⟨0⟩)
  letI := JTRelativeRowWeak.relative_weak f hW.1 hZ.1 hf
  have hw b := JTZeroCoskeletonMapping.walkingFiberMap_weak_of_relative f b
  have hdiag b := JTWalkingDiagonalTransfer.diagonalMap_weak f hW.2 hZ.2 hw b
  letI := zero_fibrant W
  letI := zero_fibrant Z
  letI : WeakEquivalence (diagramMappingPostcomp (daggerSimplex 0) f) :=
    DiagonalRecognition.weak_of_chosen_diagonal_fibers _ (zero_components_surjective f hπ) hdiag
  letI : WeakEquivalence (f.app (op ⟨0⟩)) :=
    weakEquivalence_of_precomp_of_fac (zero_natural f).symm
  letI : WeakEquivalence (rowMap f ⦋0⦌) := by
    have h : rowMap f ⦋0⦌ ≫ (rowRestrictionIso Z ⦋0⦌).hom =
        (rowRestrictionIso W ⦋0⦌).hom ≫ f.app (op ⟨0⟩) := by
      apply NatTrans.ext
      funext q x
      rfl
    exact weakEquivalence_of_postcomp_of_fac h
  letI : WeakEquivalence (rowMap f ⦋1⦌) := JTFirstRowWeakRecognition.rowOne_weak f hf
  letI : WeakEquivalence (f.app (op ⟨1⟩)) := by
    have h : rowMap f ⦋1⦌ ≫ (rowRestrictionIso Z ⦋1⦌).hom =
        (rowRestrictionIso W ⦋1⦌).hom ≫ f.app (op ⟨1⟩) := by
      apply NatTrans.ext
      funext q x
      rfl
    exact weakEquivalence_of_precomp_of_fac h.symm
  exact JTSegalRowWeakRecognition.weak_of_zero_one f hW.1 hZ.1


/-- The remaining evaluator condition at the actual ordered vertices of the
original raw fiber comparison. -/
def DecoratedEvaluatorsWeak : Prop :=
  ∀ (W : S), Localization.localObject localizingFamily W →
    ∀ x y : (row (JTStrictificationMaps.Qproj.obj W) ⦋0⦌).obj (op ⦋0⦌),
      WeakEquivalence (DecoratedNecklaceHomBar.evaluator W
        (targetVertices W x y).1 (targetVertices W x y).2)

/-- The evaluator condition gives local weakness of the original chosen
strictification by the ordered mapping-space criterion. -/
theorem chosenPsi_local_of_evaluators
    (hEval : DecoratedEvaluatorsWeak) : JTLocalizedFrameComparison.ChosenPsiWeak := by
  intro W hW
  let f := JTStrictificationInjectiveComparison.comparison W
  have hV := (injectiveLocalObject_iff_strict (JTInjectiveOrderedFiberTransfer.factor W).Z).mp
    (JTInjectiveOrderedFiberTransfer.middle_local W hW)
  have hZ := (injectiveLocalObject_iff_strict (JTStrictificationInjectiveComparison.target W)).mp
    (JTStrictificationInjectiveComparison.target_local W)
  letI := hV.1
  letI := hZ.1
  have hW' := (injectiveSegalModel_isFibrant_iff W).mpr
    ((injectiveLocalObject_iff_strict W).mp hW)
  letI : WeakEquivalence f := weak_of_ordered_fibers_and_components f hV.2 hZ.2
    (JTStrictificationInjectiveComparison.comparison_components_surjective W)
    (JTStrictificationInjectiveComparison.comparison_strictFiber_weak W hW
      (fun x y ↦ JTRawChosenFiberBridge.rawChosenFiberMapAtP_weak W x y hW'
        (hEval W hW x y)))
  apply JTStrictificationInjectiveComparison.chosenPsi_local_of_comparison_local W
  exact Localization.weakEquivalences_le_localEquivalences localizingFamily f
    ((weakEquivalence_iff f).mp inferInstance)

/-- The original four-link Theorem C follows from the same evaluator input. -/
theorem theoremC_of_evaluators
    (hEval : DecoratedEvaluatorsWeak) : TheoremCStatement.statement :=
  TheoremCStatement.statement_of_chosenPsi (chosenPsi_local_of_evaluators hEval)


private abbrev raw (W : S) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The fixed-target comma condition uses the actual target functor and
retains the specified map to each original raw necklace. -/
def TargetCommasWeaklyContractible : Prop :=
  ∀ (W : S), Localization.localObject localizingFamily W →
    ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
      (Q : NecklacesOver (raw W) (rawVertex W x) (rawVertex W y)),
      GW (pointMap (nerve (CostructuredArrow
        (DecoratedCylinderNecklacePresentation.toTarget W x y) Q)))

/-- Weak contractibility of the original fixed-target comma nerves implies
the original four-link Theorem C. -/
theorem theoremC_of_targetCommas
    (hComma : TargetCommasWeaklyContractible) : TheoremCStatement.statement := by
  apply theoremC_of_evaluators
  intro W hW x y
  let a := (targetVertices W x y).1
  let b := (targetVertices W x y).2
  exact JTTargetCommaPullbackBar.evaluator_weak_of_bar_point W a b
    (fun Q ↦ (JTTargetCommaPullbackBar.comma_point_iff_bar_point W a b Q).mp
      (hComma W hW a b Q))

end

end DaggerModels.PartII.JTRezkRecognition
