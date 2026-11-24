import DaggerModelsPartII.JTFrameNerveDetectionFromStrictification
import DaggerModelsPartII.CosimplicialMappingInvariance

/-! Weak adjoints of fibrant replacements follow from the original chosen
strictification map. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.JTFrameDerivedUnitFromStrictification

open SegalLocalizers JTFrameAdjunction JTStrictificationMaps JTStrictificationCoefficients

noncomputable section

private local instance : HasLimits DaggerSimplicialCat.{0, 0} := daggerSimplicialCatHasLimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} := daggerSimplicialCatHasColimits
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory ReverseDaggerSpace.{0} := projectiveSegalModel

private theorem projectiveWeak_eq_injectiveWeak :
    weakEquivalences ReverseDaggerSpace.{0} =
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences := by
  change projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences = _
  rw [(ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
      localizerArrow localizerArrow_mono).2,
    (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
      localizerArrow localizerArrow_mono).2]
  exact ProjectiveInjectiveComparison.localEquivalences_eq _ _

private theorem frameNerve_map_weak {C D : DaggerSimplicialCat.{0, 0}}
    [IsFibrant C] [IsFibrant D] (b : C ⟶ D)
    (hb : weakEquivalences DaggerSimplicialCat.{0, 0} b) :
    weakEquivalences ReverseDaggerSpace.{0} (frameNerve.map b) := by
  letI : adjunction.IsQuillenAdjunction := JTSegalFrameLocality.localized_isQuillenAdjunction
  letI := Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adjunction
  apply map_weak_of_trivialFibration frameNerve _ b hb
  intro A B p hp
  exact (Functor.PreservesTrivialFibrations.trivialFibrations_le frameNerve p hp).2

private theorem adjoint_weak_of_trivialCofibration (W : ReverseDaggerSpace.{0})
    (hpsi : weakEquivalences ReverseDaggerSpace.{0} (chosenPsi W))
    {C : DaggerSimplicialCat.{0, 0}} [IsFibrant C] (b : frameRealization.obj (Qproj.obj W) ⟶ C)
    (hb : trivialCofibrations DaggerSimplicialCat.{0, 0} b) :
    weakEquivalences ReverseDaggerSpace.{0} (adjunction.homEquiv _ _ b) := by
  let D := rigidCoefficient (chosenT W)
  letI : IsFibrant D := rigidCoefficient_fibrant (chosenT W)
  let a : frameRealization.obj (Qproj.obj W) ⟶ D :=
    JTCoendComparison.comparison.app (Qproj.obj W) ≫ chosenA W
  let sq : CommSq a b (terminal.from D) (terminal.from C) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  letI : HasLiftingProperty b (terminal.from D) :=
    hasLiftingProperty_of_wfs _ _ hb (mem_fibrations _)
  have ha : weakEquivalences DaggerSimplicialCat.{0, 0} a := comparison_chosenA_weak W
  have hl : weakEquivalences DaggerSimplicialCat.{0, 0} sq.lift :=
    (weakEquivalences DaggerSimplicialCat.{0, 0}).of_precomp _ _ hb.2 (sq.fac_left.symm ▸ ha)
  apply (weakEquivalences ReverseDaggerSpace.{0}).of_postcomp _
    (frameNerve.map sq.lift) (frameNerve_map_weak _ hl)
  rw [← adjunction.homEquiv_naturality_right b sq.lift, sq.fac_left]
  simpa only [Adjunction.homEquiv_unit] using hpsi

/-- Local weakness of the literal strictification implies local weakness of the
frame adjoint of every weak map from the realization of the chosen projective
replacement into a fibrant coefficient. -/
theorem frameAdjoint_weak_of_chosenPsi_weak (W : ReverseDaggerSpace.{0})
    (hpsi : injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences (chosenPsi W))
    {C : DaggerSimplicialCat.{0, 0}} [IsFibrant C] (b : frameRealization.obj (Qproj.obj W) ⟶ C)
    (hb : weakEquivalences DaggerSimplicialCat.{0, 0} b) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences (adjunction.homEquiv _ _ b) := by
  rw [← projectiveWeak_eq_injectiveWeak] at hpsi ⊢
  let d := factorizationData (trivialCofibrations DaggerSimplicialCat.{0, 0})
    (fibrations DaggerSimplicialCat.{0, 0}) b
  letI : Fibration d.p := (fibration_iff _).mpr d.hp
  letI : IsFibrant d.Z := isFibrant_of_fibration d.p
  have hp : weakEquivalences DaggerSimplicialCat.{0, 0} d.p :=
    (weakEquivalences DaggerSimplicialCat.{0, 0}).of_precomp _ _ d.hi.2 (d.fac.symm ▸ hb)
  rw [← d.fac, adjunction.homEquiv_naturality_right]
  exact (weakEquivalences ReverseDaggerSpace.{0}).comp_mem _ _
    (adjoint_weak_of_trivialCofibration W hpsi d.i d.hi) (frameNerve_map_weak _ hp)

end

end DaggerModels.PartII.JTFrameDerivedUnitFromStrictification
