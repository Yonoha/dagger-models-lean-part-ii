import DaggerModelsPartII.JTCoendMateFormula

/-! The represented Gamma generator evaluates to its literal Hom map. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite DaggerModels

namespace DaggerModels.PartII.JTFrameGeneratorCalibration

open DaggerJTAdjunction JTCoendMateFormula

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

theorem frameGeneratorEquiv_eq_native (C : DaggerSimplicialCat.{0, 0})
    (p : DaggerIndex) (f : JTFrameAdjunction.frameParameter.obj p ⟶ C) :
    frameGeneratorEquiv C p f = f := by
  letI : JTFrameAdjunction.presheafRealization.IsLeftKanExtension
      (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter) := by
    dsimp [JTFrameAdjunction.presheafRealization]
    infer_instance
  let P := uliftYoneda.{0}.obj p
  let W := representedInput p
  let Y := JTFrameAdjunction.rawPresheafNerve.obj C
  let adj := JTFrameAdjunction.presheafAdjunction.ofNatIsoRight
    JTFrameAdjunction.nativeToRawIso
  let g := (frameGeneratorIso p).inv ≫ f
  let a := adj.homEquiv (sourceEquivalence.functor.obj W) C g
  have hsource :
      sourceEquivalence.symm.toAdjunction.homEquiv P (sourceEquivalence.inverse.obj Y)
        (sourceEquivalence.toAdjunction.homEquiv W Y a) =
      sourceEquivalence.counitInv.app P ≫ a ≫ sourceEquivalence.counitInv.app Y := by
    change sourceEquivalence.counitInv.app P ≫
        sourceEquivalence.functor.map
          (sourceEquivalence.unit.app W ≫ sourceEquivalence.inverse.map a) = _
    rw [sourceEquivalence.functor.map_comp, ← sourceEquivalence.counitInv_app_functor,
      sourceEquivalence.counitInv_naturality]
  have htranspose : sourceEquivalence.counitInv.app P ≫ a =
      adj.homEquiv P C
        (JTFrameAdjunction.presheafRealization.map
          (sourceEquivalence.counitInv.app P) ≫ g) :=
    (adj.homEquiv_naturality_left _ _).symm
  unfold frameGeneratorEquiv representedEvaluation JTFrameAdjunction.adjunction
  simp only [Equiv.trans_apply, Adjunction.comp_homEquiv]
  change uliftYonedaEquiv
    (sourceEquivalence.symm.toAdjunction.homEquiv P (sourceEquivalence.inverse.obj Y)
      (sourceEquivalence.toAdjunction.homEquiv W Y a)) = f
  rw [hsource, ← Category.assoc, htranspose, uliftYonedaEquiv_comp]
  let v := JTFrameAdjunction.presheafRealization.map (sourceEquivalence.counitInv.app P) ≫ g
  have heval (z : Y.obj (op p)) : (sourceEquivalence.counitInv.app Y).app (op p) z = z := by
    change Y.map (𝟙 (op p)) z = z
    rw [Y.map_id]
    rfl
  rw [heval]
  change (adj.homEquiv P C v).app (op p) (ULift.up (𝟙 p)) = f
  dsimp only [adj, Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv,
    Equiv.trans_apply, Adjunction.equivHomsetRightOfNatIso, Equiv.coe_fn_mk,
    NatTrans.comp_app, types_comp_apply]
  change ((JTFrameAdjunction.presheafAdjunction.homEquiv P C v).app
    (op p) (ULift.up (𝟙 p))).down = f
  change (((Presheaf.uliftYonedaAdjunction JTFrameAdjunction.presheafRealization
    (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter)).homEquiv
    P C v).app (op p) (ULift.up (𝟙 p))).down = f
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  have hy : uliftYonedaEquiv.symm (ULift.up (𝟙 p)) = 𝟙 P := by
    apply uliftYonedaEquiv.injective
    exact (uliftYonedaEquiv (F := P)).apply_symm_apply (ULift.up (𝟙 p))
  rw [hy]
  change (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter).app p ≫
      JTFrameAdjunction.presheafRealization.map (𝟙 P) ≫ v = f
  rw [JTFrameAdjunction.presheafRealization.map_id]
  calc
    _ = (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter).app p ≫ v :=
      congrArg (fun h ↦
        (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter).app p ≫ h)
        (Category.id_comp v)
    _ = f := by
      change (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter).app p ≫
        (JTFrameAdjunction.presheafRealization.map (sourceEquivalence.counitInv.app P) ≫
          ((frameGeneratorIso p).inv ≫ f)) = f
      rw [← Category.assoc]
      exact Iso.hom_inv_id_assoc (frameGeneratorIso p) f

end

end DaggerModels.PartII.JTFrameGeneratorCalibration
