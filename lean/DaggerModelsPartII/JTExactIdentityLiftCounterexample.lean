import DaggerModelsPartII.JTExactSingleBeadLifts
import DaggerModelsPartII.JTZeroCoskeleton
import DaggerModelsPartII.JTSimplexUnitKan
import DaggerModelsPartII.InjectiveSegalLocality
import OriginalSimplicialPiZeroWeakEquivalence

/-!
# The uniform strict identity-lift condition fails for an injective local object

The zero coskeleton of the contractible completed simplex in degree one is
an injective local object. A raw single bead with a nonconstant endpoint
coefficient gives an empty exact identity fiber.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTContractibleCoskeleton
open SegalLocalizers JTZeroCoskeleton
noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ
private abbrev zero : J := op ⟨0⟩
private abbrev E := (evaluation J SSet.{0}).obj zero
private abbrev adj := evaluationAdjunctionLeft SSet.{0} zero

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

private theorem evaluation_preservesCofibrations : E.PreservesCofibrations := by
  constructor
  intro A B f hf
  have hm := (cofibration_iff _).mp hf
  rw [InjectiveKanDiagram.model_cofibrations] at hm
  haveI : Mono f := hm
  change Cofibration (f.app zero)
  exact (SSet.modelCategoryQuillen.cofibration_iff _).mpr
    ((NatTrans.mono_iff_mono_app f).mp inferInstance zero)

private theorem strict_of_trivialFibration {W Z : S} (q : W ⟶ Z)
    [Fibration q] [WeakEquivalence q] (hZ : IsTerminal Z) :
    unitarilyCompleteSegalCondition W := by
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos J) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos J⟩
  apply (unitarilyCompleteSegalCondition_iff_family W).mpr
  intro A B i _
  let adjA := diagramTensorMappingAdjunction A
  let adjB := diagramTensorMappingAdjunction B
  letI : adjA.IsQuillenAdjunction := InjectiveKanDiagram.diagramTensorMapping_isQuillen J A
  letI : adjB.IsQuillenAdjunction := InjectiveKanDiagram.diagramTensorMapping_isQuillen J B
  letI : (diagramMappingTarget A).PreservesTrivialFibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adjA
  letI : (diagramMappingTarget B).PreservesTrivialFibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adjB
  letI : PreservesLimitsOfSize.{0, 0} (diagramMappingTarget B) :=
    adjB.rightAdjoint_preservesLimits
  let FA := diagramMappingTarget A
  let FB := diagramMappingTarget B
  have h : diagramMappingPrecomp i W ≫ FA.map q =
      FB.map q ≫ diagramMappingPrecomp i Z := by
    apply NatTrans.ext
    funext n a
    change (Functor.whiskerRight i (tensorRight (SSet.stdSimplex.obj n.unop)) ≫ a) ≫ q = _
    exact Category.assoc _ _ _
  haveI : IsIso (diagramMappingPrecomp i Z) := by
    letI : PreservesLimitsOfSize.{0, 0} (diagramMappingTarget A) :=
      adjA.rightAdjoint_preservesLimits
    let e := (hZ.isTerminalObj FB).uniqueUpToIso (hZ.isTerminalObj FA)
    rw [(hZ.isTerminalObj FA).hom_ext (diagramMappingPrecomp i Z) e.hom]
    infer_instance
  haveI : WeakEquivalence (FA.map q) := inferInstance
  haveI : WeakEquivalence (FB.map q) := inferInstance
  exact (weakEquivalence_iff _).mp (weakEquivalence_of_postcomp_of_fac h)

theorem local_of_trivial_augmentation (K : SSet.{0})
    (hK : trivialFibrations SSet.{0} (terminal.from K)) :
    Localization.localObject localizingFamily (coskeleton.obj K) := by
  letI : coskeleton.PreservesTrivialFibrations :=
    adj.preservesTrivialFibrations_iff_preservesCofibrations.mpr evaluation_preservesCofibrations
  haveI : PreservesLimitsOfSize.{0, 0} coskeleton := adj.rightAdjoint_preservesLimits
  haveI : Fibration (terminal.from K) := (fibration_iff _).mpr hK.1
  haveI : WeakEquivalence (terminal.from K) := (weakEquivalence_iff _).mpr hK.2
  let q := coskeleton.map (terminal.from K)
  haveI : Fibration q := inferInstance
  haveI : WeakEquivalence q := inferInstance
  let h := (terminalIsTerminal : IsTerminal (⊤_ SSet.{0})).isTerminalObj coskeleton
  exact (injectiveLocalObject_iff_strict (coskeleton.obj K)).mpr
    ⟨(isFibrant_iff_of_isTerminal q h).mpr inferInstance, strict_of_trivialFibration q h⟩

end
end DaggerModels.PartII.JTContractibleCoskeleton

namespace DaggerModels.PartII.JTMovingEndpointExample

open GroupoidSimplex JTRowGraphParameterSupport JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement JTNativeRowLabel
open JTZeroCoskeleton DaggerOriginalCodiscreteNerveInjective

noncomputable section

private abbrev K := parameter.obj ⦋1⦌
private abbrev W := coskeleton.obj K
private abbrev zero : ReverseSimplexᵒᵖ := op ⟨0⟩
private abbrev I := (Δ[1] : SSet.{0})
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev s : I ⟶ K := JTCylinderCEComparison.simplexUnit.app ⦋1⦌

private def f : I ⟶ row W ⦋1⦌ :=
  s ≫ Pi.lift (fun _ : op (ReverseSimplex.inclusion.obj ⦋1⦌) ⟶ zero ↦ 𝟙 K) ≫
    (rowRestrictionIso W ⦋1⦌).inv

private def p : row W ⦋0⦌ ⟶ K :=
  (rowRestrictionIso W ⦋0⦌).hom ≫
    Pi.π (fun _ : zero ⟶ zero ↦ K) (𝟙 zero)

private theorem f_endpoint (i : Fin 2) : (f ≫ rowVertex W ⦋1⦌ i) ≫ p = s := by
  let a := (ReverseSimplex.inclusion.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).op
  have h : (rowRestrictionIso W ⦋1⦌).inv ≫ rowVertex W ⦋1⦌ i ≫
      (rowRestrictionIso W ⦋0⦌).hom = W.map a := by
    apply NatTrans.ext
    funext q x
    dsimp [rowRestrictionIso, rowVertex, row, a,
      JTRealizationDiagonal.ordinaryCurry, JTReversalInput.ordinaryInput]
    simp
  let b := Pi.lift (fun _ : op (ReverseSimplex.inclusion.obj ⦋1⦌) ⟶ zero ↦ 𝟙 K)
  let c := Pi.π (fun _ : zero ⟶ zero ↦ K) (𝟙 zero)
  have hc : W.map a ≫ c = Pi.π
      (fun _ : op (ReverseSimplex.inclusion.obj ⦋1⦌) ⟶ zero ↦ K) (a ≫ 𝟙 zero) := by
    exact Pi.lift_π _ _
  calc
    _ = s ≫ b ≫ ((rowRestrictionIso W ⦋1⦌).inv ≫ rowVertex W ⦋1⦌ i ≫
        (rowRestrictionIso W ⦋0⦌).hom) ≫ c := by
      simp only [f, p, b, c, Category.assoc]
    _ = s ≫ b ≫ W.map a ≫ c := by rw [h]
    _ = s := by rw [hc, Pi.lift_π, Category.comp_id]

private def t : I ⟶ K :=
  SSet.yonedaEquiv.symm
    (show (codiscreteNerve.obj (Fin 2)).obj (op ⦋1⦌) from Codiscrete.functor id) ≫
    (parameterCodiscreteIso.app ⦋1⦌).inv

private theorem t_label (i : Fin 2) : label t i = i := by
  unfold label t
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun z : (codiscreteNerve.obj (Fin 2)).obj (op ⦋1⦌) ↦ (z.obj i).as)
    (Equiv.apply_symm_apply SSet.yonedaEquiv (Codiscrete.functor id))

private theorem t_surjective : Function.Surjective (label t) :=
  fun i ↦ ⟨i, t_label i⟩

private theorem s_not_constant (u : (Δ[0] : SSet.{0}) ⟶ K) :
    s ≠ term I ≫ u := by
  intro h
  have hface (i : Fin 2) : vertex ⦋1⦌ i ≫ s = u := by
    rw [h, ← Category.assoc]
    have ht : vertex ⦋1⦌ i ≫ term I = 𝟙 (Δ[0] : SSet.{0}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht, Category.id_comp]
  haveI : Mono s := JTSimplexUnitKan.simplexUnit_mono ⦋1⦌
  have he := (cancel_mono s).mp ((hface 0).trans (hface 1).symm)
  unfold vertex at he
  have hj := congrArg (fun a : (Δ[0] : SSet.{0}) ⟶ I ↦
    SSet.stdSimplex.obj₀Equiv (SSet.yonedaEquiv a)) he
  dsimp only at hj
  rw [SSet.stdSimplex.yonedaEquiv_map, SSet.stdSimplex.yonedaEquiv_map] at hj
  exact (by decide : (0 : Fin 2) ≠ 1) hj

private theorem f_moving (i : Fin 2) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    f ≫ rowVertex W ⦋1⦌ i ≠ term I ≫ vertexPoint W x := by
  intro h
  apply s_not_constant (vertexPoint W x ≫ p)
  rw [← f_endpoint i, h, Category.assoc]

private abbrev x := graphRowVertex W ⦋1⦌ ⦋1⦌ f t 0
private abbrev y := graphRowVertex W ⦋1⦌ ⦋1⦌ f t 1

private def Q : NecklacesOver
    (OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W))
    (rawVertex W x) (rawVertex W y) where
  code := single 1
  map := nativeRawGraph W 1 ⦋1⦌ f t
  first := by
    have h := rawGraph_vertex W ⦋1⦌ ⦋1⦌ f t 0
    rw [← nativeVertex 1 0, Category.assoc, SSet.yonedaEquiv_comp, pointAt_vertex] at h
    exact h
  last := by
    have h := rawGraph_vertex W ⦋1⦌ ⦋1⦌ f t 1
    rw [← nativeVertex 1 1, Category.assoc, SSet.yonedaEquiv_comp, pointAt_vertex] at h
    exact h


private abbrev G : JTRowGraphRelations.Graph (JTReversalInput.ordinaryInput.obj W) ⦋1⦌ :=
  ⟨⦋1⦌, SSet.yonedaEquiv (X := row W ⦋1⦌) f, t⟩

private theorem raw_lifts_empty :
    IsEmpty (JTNativeLiftRawComparison.rawLifts Q (Over.mk (𝟙 Q.code))).Elements := by
  have h : JTRowGraphEndpointCollapse.coefficient G = f := Equiv.symm_apply_apply _ _
  refine JTRowGraphEndpointCollapse.no_identity_rawLift_of_moving_endpoint G
    t_surjective Q rfl ?_ ?_
  · exact (Category.id_comp Q.map).symm
  · rw [h]
    exact f_moving 0 x

private theorem lifts_empty :
    IsEmpty (JTTargetCommaNativeFibers.lifts Q (Over.mk (𝟙 Q.code))).Elements := by
  let e := JTNativeLiftRawComparison.rawLiftsIso Q (Over.mk (𝟙 Q.code))
  exact ⟨fun u ↦ raw_lifts_empty.false
    ((CategoryOfElements.map e.hom).obj u)⟩

/-- The uniform strict identity-lift hypothesis fails for a local object,
although the fixed-target comma can still have refinements. -/
theorem local_counterexample :
    (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
     Localization.localObject SegalLocalizers.localizingFamily W) ∧
    0 < Q.code.len ∧
    IsEmpty (JTTargetCommaNativeFibers.lifts Q (Over.mk (𝟙 Q.code))).Elements := by
  exact ⟨JTContractibleCoskeleton.local_of_trivial_augmentation K
    (augmentation_trivialFibration ⦋1⦌), by decide, lifts_empty⟩


/-- The proposed universal strict identity-lift condition is false already
for a local diagram and one nontrivial native bead. -/
theorem not_positive_length_identity_lift_condition :
    ¬ (∀ (V : SegalLocalizers.ReverseDaggerSpace.{0}),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily V) →
      ∀ (a b : (row V ⦋0⦌).obj (op ⦋0⦌))
        (P : NecklacesOver
          (OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj V))
          (rawVertex V a) (rawVertex V b)),
        0 < P.code.len →
        DaggerSSetGluing.GW (DaggerOriginalProductGadget.pointMap
          (nerve (JTTargetCommaNativeFibers.lifts P (Over.mk (𝟙 P.code))).Elements))) := by
  intro h
  obtain ⟨hW, hlen, hEmpty⟩ := local_counterexample
  let X := nerve (JTTargetCommaNativeFibers.lifts Q (Over.mk (𝟙 Q.code))).Elements
  let p := DaggerOriginalProductGadget.pointMap X
  let e := DaggerOriginalProductGadget.pointIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀
  haveI : WeakEquivalence p := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (h W hW x y Q hlen)
  let q := p ≫ e.hom
  haveI : WeakEquivalence q := by dsimp only [q]; infer_instance
  have hp := DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero q
  let v := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))
  obtain ⟨a, _⟩ := hp.2 (SSet.π₀.mk v)
  obtain ⟨u, _⟩ := SSet.π₀.mk_surjective a
  exact hEmpty.false (CategoryTheory.nerveEquiv u)

end
end DaggerModels.PartII.JTMovingEndpointExample
