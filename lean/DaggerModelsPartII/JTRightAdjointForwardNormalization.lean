import DaggerModelsPartII.JTRightAdjointOrderedFibersCore
import DaggerModelsPartII.JTXiEndpointCollapseBoundary
import DaggerModelsPartII.JTRealizationBoxCalibration
import DaggerModelsPartII.JTForwardSimplexUnit

/-!
# The represented JT mate generator is the literal forward copy

The coefficient is the image of the identity under the original
source-equivalence Yoneda bijection. We calibrate it through the chosen
free-dagger unit, the represented tensor, and the original JT box map.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTRightAdjointForwardNormalization

open DaggerJTAdjunction DaggerJTFrameUnderlying DaggerJTRepresentedFrames
open JTReversalInput JTRealizationBox JTRealizationBoxCalibration
open JTRightAdjointOrderedFibersCore JTXiEndpointCollapseBoundary

noncomputable section

/-- The actual source-equivalence counit is the identity on the represented
pair's identity coefficient after the literal currying/product-op transport. -/
private theorem representedUnitCoefficient_literal (m k : SimplexCategory) :
    representedUnitCoefficient m k =
      ULift.up (𝟙 (ReverseSimplex.inclusion.obj m), 𝟙 k) := by
  let p : DaggerIndex := (ReverseSimplex.inclusion.obj m, k)
  change JTCoendMateFormula.representedEvaluation
    (JTCoendMateFormula.representedInput p) p (𝟙 _) = _
  unfold JTCoendMateFormula.representedEvaluation
  change uliftYonedaEquiv
    ((sourceEquivalence.symm.toAdjunction.homEquiv
      (uliftYoneda.{0}.obj p) (JTCoendMateFormula.representedInput p)) (𝟙 _)) = _
  rw [Adjunction.homEquiv_unit]
  have hmap : sourceEquivalence.symm.inverse.map
      (𝟙 (sourceEquivalence.symm.functor.obj (uliftYoneda.{0}.obj p))) =
        𝟙 _ := sourceEquivalence.symm.inverse.map_id _
  rw [hmap]
  have hcomp := Category.comp_id
    (sourceEquivalence.symm.toAdjunction.unit.app (uliftYoneda.{0}.obj p))
  have hcomp' : sourceEquivalence.symm.toAdjunction.unit.app
      (uliftYoneda.{0}.obj p) ≫
        𝟙 (sourceEquivalence.symm.inverse.obj
          (sourceEquivalence.symm.functor.obj (uliftYoneda.{0}.obj p))) =
        sourceEquivalence.symm.toAdjunction.unit.app (uliftYoneda.{0}.obj p) := by
    simpa only [Functor.comp_obj] using hcomp
  rw [hcomp']
  change ((sourceEquivalence.counitInv.app (uliftYoneda.{0}.obj p)).app (op p))
    (ULift.up (𝟙 p)) = ULift.up (𝟙 p)
  rfl

/-- The represented-pair and external-box comparisons carry the chosen
coefficient to the forward reversal identity and vertical identity. -/
private theorem normalizedUnitPair (m k : SimplexCategory) :
    let p : DaggerIndex := (ReverseSimplex.inclusion.obj m, k)
    (representedOrdinaryBoxIso.app p).hom.app (op (m, k))
        ((ordinaryInput.map (representedPairIso p.1 p.2).hom).app
          (op (m, k)) (representedUnitCoefficient m k)) =
      (SSet.yonedaEquiv (forwardSimplexNat.app m),
        SSet.stdSimplex.objEquiv.symm (𝟙 k)) := by
  rw [representedUnitCoefficient_literal,
    JTForwardSimplexUnit.forwardSimplexNat_identity]
  rfl

set_option maxRecDepth 4096 in
/-- The coend mate's represented identity generator is exactly the
independently constructed full-index forward copy. -/
theorem canonicalMateForwardUnit_eq_forwardPair (m k : SimplexCategory) :
    canonicalMateForwardUnit m k = forwardPair.app (m, k) := by
  let p : DaggerIndex := (ReverseSimplex.inclusion.obj m, k)
  apply (cancel_mono (frameUnderlyingIso.app p).hom).1
  have hnat := JTRealizationGenerators.generator_naturality
    (ordinaryInput.map (representedPairIso p.1 p.2).hom)
      (m, k) (representedUnitCoefficient m k)
  change canonicalMateForwardUnit m k ≫
      (frameRepresentation.app p).hom.hom =
    JTRealizationGenerators.generator
      (ordinaryInput.obj (representedTensorPair.obj p)) (m, k)
        ((ordinaryInput.map (representedPairIso p.1 p.2).hom).app
          (op (m, k)) (representedUnitCoefficient m k)) at hnat
  let x := ((representedOrdinaryBoxIso.app p).hom.app (op (m, k))
    ((ordinaryInput.map (representedPairIso p.1 p.2).hom).app
      (op (m, k)) (representedUnitCoefficient m k)))
  have hbox := realizationBoxIso_generator
    (underlyingSimplex.obj p.1) p.2 m k x.1 x.2
  have hbox' :
      JTRealizationGenerators.generator
          (ordinaryInput.obj (representedTensorPair.obj p)) (m, k)
          ((ordinaryInput.map (representedPairIso p.1 p.2).hom).app
            (op (m, k)) (representedUnitCoefficient m k)) ≫
            (representedBoxUnderlyingIso p).hom =
        SSet.yonedaEquiv.symm x.1 ⊗ₘ
          GroupoidSimplex.parameter.map (SSet.stdSimplex.objEquiv x.2) := by
    simpa [x, representedBoxUnderlyingIso, representedOrdinaryBoxIso] using hbox
  have hn : canonicalMateForwardUnit m k ≫ (frameUnderlyingIso.app p).hom =
      forwardSimplexNat.app m ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k) := by
    change canonicalMateForwardUnit m k ≫
      ((frameRepresentation.app p).hom.hom ≫
        (representedBoxUnderlyingIso p).hom) = _
    rw [← Category.assoc, hnat, hbox']
    rw [show x = (SSet.yonedaEquiv (forwardSimplexNat.app m),
        SSet.stdSimplex.objEquiv.symm (𝟙 k)) from normalizedUnitPair m k]
    have h₁ : SSet.yonedaEquiv.symm (SSet.yonedaEquiv (forwardSimplexNat.app m)) =
        forwardSimplexNat.app m :=
      Equiv.symm_apply_apply SSet.yonedaEquiv (forwardSimplexNat.app m)
    have h₂ : SSet.stdSimplex.objEquiv.{0}
        (SSet.stdSimplex.objEquiv.{0}.symm (𝟙 k)) = 𝟙 k :=
      Equiv.apply_symm_apply SSet.stdSimplex.objEquiv.{0} (𝟙 k)
    have h₂' : GroupoidSimplex.parameter.map
        (SSet.stdSimplex.objEquiv.{0}
          (SSet.stdSimplex.objEquiv.{0}.symm (𝟙 k))) =
          𝟙 (GroupoidSimplex.parameter.obj k) := by
      rw [h₂]
      exact GroupoidSimplex.parameter.map_id k
    exact congrArg₂ (fun a b ↦ a ⊗ₘ b) h₁ h₂'
  have hf : forwardPair.app (m, k) ≫ (frameUnderlyingIso.app p).hom =
      forwardSimplexNat.app m ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k) := by
    change (forwardSimplexNat.app m ⊗ₘ
        𝟙 (GroupoidSimplex.parameter.obj k)) ≫
          (frameUnderlyingIso.app p).inv ≫
            (frameUnderlyingIso.app p).hom = _
    let f := forwardSimplexNat.app m ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)
    have hi : (frameUnderlyingIso.app p).inv ≫
        (frameUnderlyingIso.app p).hom = 𝟙 _ :=
      Iso.inv_hom_id (frameUnderlyingIso.app p)
    calc
      _ = f ≫ ((frameUnderlyingIso.app p).inv ≫
            (frameUnderlyingIso.app p).hom) := Category.assoc _ _ _
      _ = f ≫ 𝟙 _ := congrArg (fun e ↦ f ≫ e) hi
      _ = _ := Category.comp_id _
  exact hn.trans hf.symm

/-- Under the two original represented adjunctions, the actual underlying
right comparison is literal precomposition by the full-index forward copy. -/
theorem comparison_on_represented_forward (X : DaggerSSet.{0})
    (m k : SimplexCategory)
    (f : frame.obj (ReverseSimplex.inclusion.obj m, k) ⟶ X) :
    (((JTUnderlyingRightComparison.comparison.app X).app (op (m, k)))
      (daggerGeneratorEquiv X (ReverseSimplex.inclusion.obj m) k f)).down =
        forwardPair.app (m, k) ≫ f.hom := by
  rw [comparison_on_represented, canonicalMateForwardUnit_eq_forwardPair]

end

end DaggerModels.PartII.JTRightAdjointForwardNormalization
