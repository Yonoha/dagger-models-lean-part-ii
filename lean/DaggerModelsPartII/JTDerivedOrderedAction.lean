import DaggerModelsPartII.JTDerivedOrderedMate
import DaggerModelsPartII.ArrowReedyCornerInterchange
import DaggerModelsPartII.ReedyCoefficientChange
import DaggerModelsPartII.StrictFrameMappingWeak
import DaggerModelsPartII.StrictFrameMappingFibration
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Componentwise homotopy invariance for the literal Gamma endpoint arrow

The original endpoint arrow and its zero-fixed replacement are compared on
both cosimplicial components before taking an ordered endpoint fiber.  This
does not identify a raw strict fiber with the derived ordered fiber.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTDerivedOrderedAction

open JTRelativeReedyFrame JTEndpointArrowReplacement JTOrderedFrameMate
open ArrowReedyCornerInterchange JTActualCosimplicialFrame JTZeroObjects
open JTEndpointAugmentations JTEndpointCobaseAugmentations

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) :=
  simplicialReedyModelCategory Coefficientᵒᵖ

private def L : (Arrow Coefficient)ᵒᵖ ⥤ Coefficientᵒᵖ :=
  (Arrow.leftFunc (C := Coefficient)).op

private def R : (Arrow Coefficient)ᵒᵖ ⥤ Coefficientᵒᵖ :=
  (Arrow.rightFunc (C := Coefficient)).op

private local instance : PreservesLimitsOfSize.{0, 0} L := by
  letI : PreservesColimitsOfSize.{0, 0} (Arrow.leftFunc (C := Coefficient)) :=
    ⟨fun {_} _ ↦ inferInstance⟩
  exact preservesLimitsOfSize_op _

def gammaSourceOp : SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ := G.op ⋙ L
def gammaTargetOp : SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ := G.op ⋙ R
def qGammaSourceOp : SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ := QGop ⋙ L
def qGammaTargetOp : SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ := QGop ⋙ R

def qGammaSource : gammaSourceOp ⟶ qGammaSourceOp :=
  Functor.whiskerRight (NatTrans.op qG) L

def qGammaTarget : gammaTargetOp ⟶ qGammaTargetOp :=
  Functor.whiskerRight (NatTrans.op qG) R

private def opCoprodIsoProd (X Y : Coefficient) :
    op (X ⨿ Y) ≅ op X ⨯ op Y where
  hom := prod.lift (coprod.inl : X ⟶ X ⨿ Y).op
    (coprod.inr : Y ⟶ X ⨿ Y).op
  inv := (coprod.desc
    (prod.fst : op X ⨯ op Y ⟶ op X).unop
    (prod.snd : op X ⨯ op Y ⟶ op Y).unop).op
  hom_inv_id := by
    apply Quiver.Hom.unop_inj
    change (coprod.desc prod.fst.unop prod.snd.unop) ≫
      (prod.lift (coprod.inl : X ⟶ X ⨿ Y).op
        (coprod.inr : Y ⟶ X ⨿ Y).op).unop = 𝟙 (X ⨿ Y)
    apply (coprod.hom_ext (X := X) (Y := Y))
    · rw [← Category.assoc, coprod.inl_desc, Category.comp_id]
      calc
        (prod.fst : op X ⨯ op Y ⟶ op X).unop ≫
            (prod.lift (coprod.inl : X ⟶ X ⨿ Y).op
              (coprod.inr : Y ⟶ X ⨿ Y).op).unop =
            (prod.lift (coprod.inl : X ⟶ X ⨿ Y).op
              (coprod.inr : Y ⟶ X ⨿ Y).op ≫
              (prod.fst : op X ⨯ op Y ⟶ op X)).unop := rfl
        _ = coprod.inl.op.unop := congrArg Quiver.Hom.unop
          (prod.lift_fst (coprod.inl : X ⟶ X ⨿ Y).op
            (coprod.inr : Y ⟶ X ⨿ Y).op)
        _ = coprod.inl := rfl
    · rw [← Category.assoc, coprod.inr_desc, Category.comp_id]
      calc
        (prod.snd : op X ⨯ op Y ⟶ op Y).unop ≫
            (prod.lift (coprod.inl : X ⟶ X ⨿ Y).op
              (coprod.inr : Y ⟶ X ⨿ Y).op).unop =
            (prod.lift (coprod.inl : X ⟶ X ⨿ Y).op
              (coprod.inr : Y ⟶ X ⨿ Y).op ≫
              (prod.snd : op X ⨯ op Y ⟶ op Y)).unop := rfl
        _ = coprod.inr.op.unop := congrArg Quiver.Hom.unop
          (prod.lift_snd (coprod.inl : X ⟶ X ⨿ Y).op
            (coprod.inr : Y ⟶ X ⨿ Y).op)
        _ = coprod.inr := rfl
  inv_hom_id := by
    apply (prod.hom_ext (X := op X) (Y := op Y))
    · simp only [Category.assoc, prod.lift_fst, ← op_comp,
        coprod.inl_desc, Quiver.Hom.op_unop, Category.id_comp]
    · simp only [Category.assoc, prod.lift_snd, ← op_comp,
        coprod.inr_desc, Quiver.Hom.op_unop, Category.id_comp]

set_option maxHeartbeats 1000000 in
/-- The two ordered endpoint copies become a product after taking opposites.
This is an isomorphism of the full cosimplicial diagrams, not just values. -/
private def gammaSourceProductIso :
    gammaSourceOp ≅
      (GammaOuter.obj zeroIndex).op ⨯ (GammaOuter.obj zeroIndex).op :=
  NatIso.ofComponents (fun k ↦ by
    let H := (GammaOuter.obj zeroIndex).op
    let E := (evaluation SimplexCategoryᵒᵖ Coefficientᵒᵖ).obj k
    letI : PreservesLimit (pair H H) E := inferInstance
    have hs : gammaSourceOp.obj k =
        op ((Gamma.obj k.unop).obj zeroIndex ⨿
          (Gamma.obj k.unop).obj zeroIndex) := rfl
    exact eqToIso hs ≪≫
      opCoprodIsoProd ((Gamma.obj k.unop).obj zeroIndex)
        ((Gamma.obj k.unop).obj zeroIndex) ≪≫
      (PreservesLimitPair.iso E H H).symm) (by
    intro s t θ
    let H := (GammaOuter.obj zeroIndex).op
    let Et := (evaluation SimplexCategoryᵒᵖ Coefficientᵒᵖ).obj t
    letI : PreservesLimit (pair H H) Et := inferInstance
    rw [← cancel_mono (PreservesLimitPair.iso Et H H).hom]
    dsimp only [Et, H]
    apply prod.hom_ext
    · simp only [Iso.trans_hom, Iso.symm_hom,
        eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [PreservesLimitPair.iso_hom, prodComparison_fst]
      have heval :
          ((evaluation SimplexCategoryᵒᵖ Coefficientᵒᵖ).obj t).map
            (prod.fst : H ⨯ H ⟶ H) =
          (prod.fst : H ⨯ H ⟶ H).app t := rfl
      rw [heval]
      rw [(prod.fst : H ⨯ H ⟶ H).naturality θ]
      have hevalS :
          ((evaluation SimplexCategoryᵒᵖ Coefficientᵒᵖ).obj s).map
            (prod.fst : H ⨯ H ⟶ H) =
          (prod.fst : H ⨯ H ⟶ H).app s := rfl
      rw [← hevalS]
      rw [PreservesLimitPair.iso_inv_fst_assoc]
      simp [gammaSourceOp, G, JTEndpointHom.endpointSource,
        opCoprodIsoProd]
      let Xt := (Gamma.obj t.unop).obj zeroIndex
      let Xs := (Gamma.obj s.unop).obj zeroIndex
      let f : Xt ⟶ Xs := (Gamma.map θ.unop).app zeroIndex
      change (coprod.map f f).op ≫
          (prod.lift (coprod.inl : Xt ⟶ Xt ⨿ Xt).op
            (coprod.inr : Xt ⟶ Xt ⨿ Xt).op ≫
              (prod.fst : op Xt ⨯ op Xt ⟶ op Xt)) =
        (prod.lift (coprod.inl : Xs ⟶ Xs ⨿ Xs).op
            (coprod.inr : Xs ⟶ Xs ⨿ Xs).op ≫
              (prod.fst : op Xs ⨯ op Xs ⟶ op Xs)) ≫ f.op
      simp only [prod.lift_fst]
      exact congrArg Quiver.Hom.op (coprod.inl_map f f)
    · simp only [Iso.trans_hom, Iso.symm_hom,
        eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [PreservesLimitPair.iso_hom, prodComparison_snd]
      have heval :
          ((evaluation SimplexCategoryᵒᵖ Coefficientᵒᵖ).obj t).map
            (prod.snd : H ⨯ H ⟶ H) =
          (prod.snd : H ⨯ H ⟶ H).app t := rfl
      rw [heval]
      rw [(prod.snd : H ⨯ H ⟶ H).naturality θ]
      have hevalS :
          ((evaluation SimplexCategoryᵒᵖ Coefficientᵒᵖ).obj s).map
            (prod.snd : H ⨯ H ⟶ H) =
          (prod.snd : H ⨯ H ⟶ H).app s := rfl
      rw [← hevalS]
      rw [PreservesLimitPair.iso_inv_snd_assoc]
      simp [gammaSourceOp, G, JTEndpointHom.endpointSource,
        opCoprodIsoProd]
      let Xt := (Gamma.obj t.unop).obj zeroIndex
      let Xs := (Gamma.obj s.unop).obj zeroIndex
      let f : Xt ⟶ Xs := (Gamma.map θ.unop).app zeroIndex
      change (coprod.map f f).op ≫
          (prod.lift (coprod.inl : Xt ⟶ Xt ⨿ Xt).op
            (coprod.inr : Xt ⟶ Xt ⨿ Xt).op ≫
              (prod.snd : op Xt ⨯ op Xt ⟶ op Xt)) =
        (prod.lift (coprod.inl : Xs ⟶ Xs ⨿ Xs).op
            (coprod.inr : Xs ⟶ Xs ⨿ Xs).op ≫
              (prod.snd : op Xs ⨯ op Xs ⟶ op Xs)) ≫ f.op
      simp only [prod.lift_snd]
      exact congrArg Quiver.Hom.op (coprod.inr_map f f))

/-- The original Gamma source is the coproduct of two Reedy cofibrant
frames, so its opposite is Reedy fibrant. -/
private theorem gammaSource_fibrant : IsFibrant gammaSourceOp := by
  let H := (GammaOuter.obj zeroIndex).op
  letI : IsFibrant H := GammaOuter_op_isFibrant zeroIndex
  have hprod : IsFibrant (H ⨯ H) := by
    haveI : Fibration (prod.fst : H ⨯ H ⟶ H) := inferInstance
    exact isFibrant_of_fibration (prod.fst : H ⨯ H ⟶ H)
  letI : IsFibrant (H ⨯ H) := hprod
  haveI : Fibration gammaSourceProductIso.hom := inferInstance
  exact isFibrant_of_fibration gammaSourceProductIso.hom

/-- The original Gamma target cosimplicial component is Reedy cofibrant. -/
private theorem gammaTarget_fibrant : IsFibrant gammaTargetOp := by
  change IsFibrant (GammaOuter.obj oneIndex).op
  exact GammaOuter_op_isFibrant oneIndex

/-- The projective Arrow matching condition makes the replacement source
cosimplicial component Reedy cofibrant. -/
private theorem qGammaSource_fibrant : IsFibrant qGammaSourceOp := by
  let t := Functor.whiskerRight firstRight L
  have ht : IsTerminal ((⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ)) ⋙ L) :=
    terminalIsTerminal.isTerminalObj
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ
        (Arrow Coefficient)ᵒᵖ Coefficientᵒᵖ).obj L) _
  apply (isFibrant_iff_of_isTerminal t ht).mpr
  apply (fibration_iff t).mpr
  intro n
  apply (ReedyCoefficientChange.relativeMatchingMap_property_iff
    (fibrations Coefficientᵒᵖ) L n firstRight).mp
  rw [fibrations_op]
  exact (firstRight_relative n).1

/-- The relative endpoint-face cofibration makes the replacement target
cosimplicial component Reedy cofibrant as well. -/
private theorem qGammaTarget_fibrant : IsFibrant qGammaTargetOp := by
  letI : IsFibrant (sourceOpp QGop) := qGammaSource_fibrant
  have hf : Fibration (structureOpp QGop) := by
    apply (fibration_iff _).mpr
    intro n
    rw [fibrations_op]
    exact ArrowReedyCornerInterchange.Actual.QG_relativeCofibration n
  exact isFibrant_of_fibration (structureOpp QGop)

/-- The actual first replacement is weak on the source component as a
map in the opposite Reedy diagram model. -/
private theorem qGammaSource_weak :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) qGammaSource := by
  intro k
  rw [weakEquivalences_op]
  change weakEquivalences Coefficient ((qG.app k.unop).left)
  have hk : ⦋k.unop.len⦌ = k.unop := SimplexCategory.ext _ _ rfl
  rw [← hk]
  exact (qG_pointwiseWeak k.unop.len).1

/-- The same first replacement is weak on the target component. -/
private theorem qGammaTarget_weak :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) qGammaTarget := by
  intro k
  rw [weakEquivalences_op]
  change weakEquivalences Coefficient ((qG.app k.unop).right)
  have hk : ⦋k.unop.len⦌ = k.unop := SimplexCategory.ext _ _ rfl
  rw [← hk]
  exact (qG_pointwiseWeak k.unop.len).2

/-- Every structure map of the first replacement's source component is
original weak, by its actual augmentation to the constant boundary. -/
theorem qGammaSource_maps_weak
    {s t : SimplexCategoryᵒᵖ} (θ : s ⟶ t) :
    weakEquivalences Coefficientᵒᵖ (qGammaSourceOp.map θ) := by
  rw [weakEquivalences_op]
  let P := weakEquivalences Coefficient
  have hs : P ((sourceAug QGaugmentation).app s.unop) := by
    have hs : ⦋s.unop.len⦌ = s.unop := SimplexCategory.ext _ _ rfl
    rw [← hs]
    exact (QGaugmentation_weak s.unop.len).1
  have ht : P ((sourceAug QGaugmentation).app t.unop) := by
    have ht : ⦋t.unop.len⦌ = t.unop := SimplexCategory.ext _ _ rfl
    rw [← ht]
    exact (QGaugmentation_weak t.unop.len).1
  have h := (sourceAug QGaugmentation).naturality θ.unop
  change (qGammaSourceOp.map θ).unop ≫
      (sourceAug QGaugmentation).app s.unop =
        (sourceAug QGaugmentation).app t.unop ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact P.of_postcomp _ _ hs (h.symm ▸ ht)

/-- Every structure map of its target component is weak by the actual
augmentation to the original rigidified interval. -/
theorem qGammaTarget_maps_weak
    {s t : SimplexCategoryᵒᵖ} (θ : s ⟶ t) :
    weakEquivalences Coefficientᵒᵖ (qGammaTargetOp.map θ) := by
  rw [weakEquivalences_op]
  let P := weakEquivalences Coefficient
  have hs : P ((targetAug QGaugmentation).app s.unop) := by
    have hs : ⦋s.unop.len⦌ = s.unop := SimplexCategory.ext _ _ rfl
    rw [← hs]
    exact (QGaugmentation_weak s.unop.len).2
  have ht : P ((targetAug QGaugmentation).app t.unop) := by
    have ht : ⦋t.unop.len⦌ = t.unop := SimplexCategory.ext _ _ rfl
    rw [← ht]
    exact (QGaugmentation_weak t.unop.len).2
  have h := (targetAug QGaugmentation).naturality θ.unop
  change (qGammaTargetOp.map θ).unop ≫
      (targetAug QGaugmentation).app s.unop =
        (targetAug QGaugmentation).app t.unop ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact P.of_postcomp _ _ hs (h.symm ▸ ht)

/-- Mapping into an original fibrant coefficient sends the source component
of the actual qG replacement to a Kan weak equivalence. -/
theorem gamma_source_mapping_weak (C : Coefficient) [IsFibrant C] :
    weakEquivalences SSet.{0}
      ((StrictFrameMappingWeak.strictMapping C).map qGammaSource) := by
  letI : IsFibrant gammaSourceOp := gammaSource_fibrant
  letI : IsFibrant qGammaSourceOp := qGammaSource_fibrant
  exact StrictFrameMappingWeak.strictMapping_map_weak C qGammaSource qGammaSource_weak

/-- The target component of that same actual replacement also induces a
Kan weak equivalence on strict mapping simplicial sets. -/
theorem gamma_target_mapping_weak (C : Coefficient) [IsFibrant C] :
    weakEquivalences SSet.{0}
      ((StrictFrameMappingWeak.strictMapping C).map qGammaTarget) := by
  letI : IsFibrant gammaTargetOp := gammaTarget_fibrant
  letI : IsFibrant qGammaTargetOp := qGammaTarget_fibrant
  exact StrictFrameMappingWeak.strictMapping_map_weak C qGammaTarget qGammaTarget_weak

/-- The resolved endpoint map is an actual Kan fibration on strict mapping
simplicial sets. Its fiber therefore models the chosen ordered homotopy fiber
once the two componentwise weak maps above are used. -/
theorem qGamma_mapping_fibration (C : Coefficient) [IsFibrant C] :
    Fibration ((StrictFrameMappingWeak.strictMapping C).map (structureOpp QGop)) := by
  letI : IsFibrant qGammaSourceOp := qGammaSource_fibrant
  letI : IsFibrant qGammaTargetOp := qGammaTarget_fibrant
  exact StrictFrameMappingFibration.strictMapping_map_fibration C
    (fun θ ↦ qGammaTarget_maps_weak θ)
    (fun θ ↦ qGammaSource_maps_weak θ)
    (structureOpp QGop)
    (fun n ↦ by
      rw [fibrations_op]
      exact ArrowReedyCornerInterchange.Actual.QG_relativeCofibration n)

/-- The two componentwise weak maps respect the actual ordered endpoint
face arrow. The square precedes any strict or homotopy fiber construction. -/
theorem gamma_mapping_square (C : Coefficient) :
    (StrictFrameMappingWeak.strictMapping C).map (structureOpp G.op) ≫
      (StrictFrameMappingWeak.strictMapping C).map qGammaSource =
    (StrictFrameMappingWeak.strictMapping C).map qGammaTarget ≫
      (StrictFrameMappingWeak.strictMapping C).map (structureOpp QGop) := by
  have h : structureOpp G.op ≫ qGammaSource =
      qGammaTarget ≫ structureOpp QGop := by
    apply NatTrans.ext
    funext k
    change ((qG.app k.unop).left ≫ (G.obj k.unop).hom).op =
      ((QG.obj k.unop).hom ≫ (qG.app k.unop).right).op
    exact congrArg Quiver.Hom.op (Arrow.w (qG.app k.unop))
  simpa only [Functor.map_comp] using
    congrArg ((StrictFrameMappingWeak.strictMapping C).map) h

end

end DaggerModels.PartII.JTDerivedOrderedAction
