import DaggerModelsPartII.JTCoendMateFormula
import DaggerModelsPartII.RepresentableTensorAdjunction
import DaggerModelsPartII.JTOrdinaryLocalCobase
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Actual projective free-weight JT realization

This file connects a free outer simplicial diagram with the actual
cosimplicial Gamma and Xi frames, naturally in its simplicial-set weight.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerModels.PartII

namespace DaggerModels.PartII.JTProjectiveGeneratorRealization

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

/-- The actual outer free functor, for an arbitrary simplicial-set weight. -/
def outerFree (m : ReverseSimplex) :
    SSet.{0} ⥤ SegalLocalizers.ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.free ReverseSimplexᵒᵖ (op m)

/-- The source free-weight realization and evaluation adjunction. -/
def gammaFreeAdjunction (m : ReverseSimplex) :
    outerFree m ⋙ JTFrameAdjunction.frameRealization ⊣
      JTFrameAdjunction.frameNerve ⋙
        (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m) :=
  (evaluationAdjunctionRight SSet.{0} (op m)).comp JTFrameAdjunction.adjunction

/-- The target free-weight realization and evaluation adjunction. -/
def xiFreeAdjunction (m : ReverseSimplex) :
    outerFree m ⋙
      (DaggerJTRealization.daggerRealization ⋙
        OrdinaryRigidification.DaggerRigidification.daggerRigidification) ⊣
      JTCoendMate.compositeNerve ⋙
        (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m) :=
  (evaluationAdjunctionRight SSet.{0} (op m)).comp
    JTCoendMate.compositeAdjunction

/-- The vertical Yoneda realization of the actual Gamma frame. -/
def gammaWeighted (m : ReverseSimplex) : SSet.{0} ⥤ DaggerSimplicialCat.{0, 0} :=
  uliftYoneda.{0}.leftKanExtension (JTRelativeReedyFrame.GammaOuter.obj m)

/-- Evaluation of the actual frame nerve is the native restricted Yoneda nerve. -/
def gammaNerveIso (m : ReverseSimplex) :
    JTFrameAdjunction.frameNerve ⋙
      (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m) ≅
        Presheaf.restrictedULiftYoneda.{0}
          (JTRelativeReedyFrame.GammaOuter.obj m) :=
  NatIso.ofComponents
    (fun C ↦ NatIso.ofComponents
      (fun k ↦ (Equiv.ulift.symm :
        ((JTRelativeReedyFrame.GammaOuter.obj m).obj k.unop ⟶ C) ≃
          ULift ((JTRelativeReedyFrame.GammaOuter.obj m).obj k.unop ⟶ C)).toIso)
      (by
        intro k l f
        ext x
        change ULift.up
          (JTFrameAdjunction.frameParameter.map
            (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, f.unop)) ≫ x) =
          ULift.up ((JTRelativeReedyFrame.GammaOuter.obj m).map f.unop ≫ x)
        rw [JTFrameAdjunction.frameParameter_vertical_map]))
    (by intro C D f; ext k x; rfl)

/-- The weighted Gamma realization has its native restricted-Yoneda adjunction. -/
def gammaWeightedAdjunction (m : ReverseSimplex) :
    gammaWeighted m ⊣
      Presheaf.restrictedULiftYoneda.{0}
        (JTRelativeReedyFrame.GammaOuter.obj m) := by
  letI : (gammaWeighted m).IsLeftKanExtension
      (uliftYoneda.{0}.leftKanExtensionUnit
        (JTRelativeReedyFrame.GammaOuter.obj m)) := by
    dsimp [gammaWeighted]
    infer_instance
  exact Presheaf.uliftYonedaAdjunction
    (gammaWeighted m)
    (uliftYoneda.{0}.leftKanExtensionUnit (JTRelativeReedyFrame.GammaOuter.obj m))

/-- The actual Xi frame with the outer reversal index fixed. -/
def xiVertical (m : ReverseSimplex) :
    SimplexCategory ⥤ DaggerSimplicialCat.{0, 0} :=
  (Functor.curry.obj RigidifiedJTFrames.Xi).obj m

/-- The vertical Yoneda realization of the actual Xi frame. -/
def xiWeighted (m : ReverseSimplex) : SSet.{0} ⥤ DaggerSimplicialCat.{0, 0} :=
  uliftYoneda.{0}.leftKanExtension (xiVertical m)

/-- The native weighted Xi realization and restricted-Yoneda nerve are adjoint. -/
def xiWeightedAdjunction (m : ReverseSimplex) :
    xiWeighted m ⊣ Presheaf.restrictedULiftYoneda.{0} (xiVertical m) := by
  letI : (xiWeighted m).IsLeftKanExtension
      (uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m)) := by
    dsimp [xiWeighted]
    infer_instance
  exact Presheaf.uliftYonedaAdjunction
    (xiWeighted m) (uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m))

/-- Evaluation of the composite nerve is the restricted Yoneda nerve of Xi. -/
def xiNerveIso (m : ReverseSimplex) :
    JTCoendMate.compositeNerve ⋙
      (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m) ≅
        Presheaf.restrictedULiftYoneda.{0} (xiVertical m) :=
  NatIso.ofComponents
    (fun C ↦ NatIso.ofComponents
      (fun k ↦
        let e := DaggerActualRigidificationQuillen.adjunction.homEquiv
          (DaggerJTAdjunction.frame.obj (m, k.unop)) C
        (show ((JTCoendMate.compositeNerve ⋙
          (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m)).obj C).obj k ≃
          ((Presheaf.restrictedULiftYoneda.{0} (xiVertical m)).obj C).obj k from
          { toFun := fun x ↦ ⟨e.symm x.down⟩
            invFun := fun x ↦ ⟨e x.down⟩
            left_inv := by intro x; cases x; simp
            right_inv := by intro x; cases x; simp }).toIso)
      (by
        intro k l f
        ext x
        let p : (m, l.unop) ⟶ (m, k.unop) := (𝟙 m, f.unop)
        change ULift.up
            ((DaggerActualRigidificationQuillen.adjunction.homEquiv
              (DaggerJTAdjunction.frame.obj (m, l.unop)) C).symm
                (DaggerJTAdjunction.frame.map p ≫ x.down)) =
          ULift.up
            ((xiVertical m).map f.unop ≫
              (DaggerActualRigidificationQuillen.adjunction.homEquiv
                (DaggerJTAdjunction.frame.obj (m, k.unop)) C).symm x.down)
        exact congrArg ULift.up
          (DaggerActualRigidificationQuillen.adjunction.homEquiv_naturality_left_symm
            (DaggerJTAdjunction.frame.map p) x.down)))
    (by
      intro C D f
      ext k x
      change ULift.up
          ((DaggerActualRigidificationQuillen.adjunction.homEquiv
            (DaggerJTAdjunction.frame.obj (m, k.unop)) D).symm
              (x.down ≫ OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.map f)) =
        ULift.up
          ((DaggerActualRigidificationQuillen.adjunction.homEquiv
            (DaggerJTAdjunction.frame.obj (m, k.unop)) C).symm x.down ≫ f)
      exact congrArg ULift.up
        (DaggerActualRigidificationQuillen.adjunction.homEquiv_naturality_right_symm
          x.down f))

/-- A two-index represented input is the actual outer free diagram on a simplex. -/
def representedInputFreeIso (m : ReverseSimplex) (k : SimplexCategory) :
    JTCoendMateFormula.representedInput (m, k) ≅
      (outerFree m).obj (SSet.stdSimplex.obj k) :=
  DaggerJTRepresentedFrames.representedPairIso m k ≪≫
    (representableTensorIsoFree m).app (SSet.stdSimplex.obj k)

/-- The represented-input/free-simplex identification is natural in the vertical index. -/
def representedInputFreeNatIso (m : ReverseSimplex) :
    (Functor.curry.obj DaggerJTRepresentedFrames.representedPair).obj m ≅
      SSet.stdSimplex ⋙ outerFree m :=
  NatIso.ofComponents (representedInputFreeIso m) (by
    intro k l f
    have hPair := DaggerJTRepresentedFrames.representedPairNatIso.hom.naturality
      (show (m, k) ⟶ (m, l) from (𝟙 m, f))
    change DaggerJTRepresentedFrames.representedPair.map (𝟙 m, f) ≫
        (DaggerJTRepresentedFrames.representedPairIso m l).hom =
      (DaggerJTRepresentedFrames.representedPairIso m k).hom ≫
        DaggerJTRepresentedFrames.representedTensorPair.map (𝟙 m, f) at hPair
    dsimp only [representedInputFreeIso, Iso.trans_hom]
    change
      (DaggerJTRepresentedFrames.representedPair.map (𝟙 m, f) ≫
          (DaggerJTRepresentedFrames.representedPairIso m l).hom) ≫
        ((representableTensorIsoFree m).app (SSet.stdSimplex.obj l)).hom =
      ((DaggerJTRepresentedFrames.representedPairIso m k).hom ≫
          ((representableTensorIsoFree m).app (SSet.stdSimplex.obj k)).hom) ≫
        (outerFree m).map (SSet.stdSimplex.map f)
    rw [hPair, Category.assoc]
    simp [DaggerJTRepresentedFrames.representedTensorPair,
      DaggerJTRepresentedFrames.representedPair, outerFree,
      representableTensor])

/-- The full two-index Yoneda unit, transported through the source equivalence. -/
def frameRepresentedPairIso :
    JTFrameAdjunction.frameParameter ≅
      DaggerJTRepresentedFrames.representedPair ⋙
        JTFrameAdjunction.frameRealization :=
  asIso (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter) ≪≫
    Functor.isoWhiskerRight
      (uliftYoneda.{0}.rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft uliftYoneda.{0}
          DaggerJTAdjunction.sourceEquivalence.counitIso.symm ≪≫
        (Functor.associator uliftYoneda.{0}
          DaggerJTAdjunction.sourceEquivalence.inverse
          DaggerJTAdjunction.sourceEquivalence.functor).symm)
      JTFrameAdjunction.presheafRealization ≪≫
    Functor.associator
      (uliftYoneda.{0} ⋙ DaggerJTAdjunction.sourceEquivalence.inverse)
      DaggerJTAdjunction.sourceEquivalence.functor
      JTFrameAdjunction.presheafRealization

/-- The original target represented pair has only associator coherence. -/
def xiRepresentedPairIso :
    RigidifiedJTFrames.Xi ≅
      DaggerJTRepresentedFrames.representedPair ⋙
        (DaggerJTRealization.daggerRealization ⋙
          OrdinaryRigidification.DaggerRigidification.daggerRigidification) :=
  Functor.isoWhiskerRight
    (Functor.associator uliftYoneda.{0}
      DaggerJTAdjunction.sourceEquivalence.inverse
      DaggerJTRealization.daggerRealization).symm
    OrdinaryRigidification.DaggerRigidification.daggerRigidification ≪≫
      Functor.associator
        (uliftYoneda.{0} ⋙ DaggerJTAdjunction.sourceEquivalence.inverse)
        DaggerJTRealization.daggerRealization
        OrdinaryRigidification.DaggerRigidification.daggerRigidification

private def fixedRepresentedFreeNatIso
    (L : SegalLocalizers.ReverseDaggerSpace.{0} ⥤ DaggerSimplicialCat.{0, 0})
    (A : DaggerJTAdjunction.DaggerIndex ⥤ DaggerSimplicialCat.{0, 0})
    (e : A ≅ DaggerJTRepresentedFrames.representedPair ⋙ L)
    (m : ReverseSimplex) :
    (Functor.curry.obj A).obj m ≅ SSet.stdSimplex ⋙ (outerFree m ⋙ L) :=
  NatIso.ofComponents
    (fun k ↦ e.app (m, k) ≪≫ L.mapIso (representedInputFreeIso m k)) (by
      intro k l f
      have hE := e.hom.naturality (show (m, k) ⟶ (m, l) from (𝟙 m, f))
      have hR := (representedInputFreeNatIso m).hom.naturality f
      change A.map (𝟙 m, f) ≫ (e.app (m, l)).hom =
        (e.app (m, k)).hom ≫
          L.map (DaggerJTRepresentedFrames.representedPair.map (𝟙 m, f)) at hE
      change DaggerJTRepresentedFrames.representedPair.map (𝟙 m, f) ≫
          (representedInputFreeIso m l).hom =
        (representedInputFreeIso m k).hom ≫
          (outerFree m).map (SSet.stdSimplex.map f) at hR
      dsimp only [Iso.trans_hom, Functor.mapIso_hom]
      change
        (A.map (𝟙 m, f) ≫ (e.app (m, l)).hom) ≫
          L.map (representedInputFreeIso m l).hom =
        ((e.app (m, k)).hom ≫ L.map (representedInputFreeIso m k).hom) ≫
          L.map ((outerFree m).map (SSet.stdSimplex.map f))
      rw [hE, Category.assoc, ← L.map_comp]
      rw [hR, L.map_comp, Category.assoc])

/-- The actual Gamma frame is the represented restriction of its free-weight realization. -/
def gammaFreeRepresentation (m : ReverseSimplex) :
    JTRelativeReedyFrame.GammaOuter.obj m ≅
      SSet.stdSimplex ⋙ (outerFree m ⋙ JTFrameAdjunction.frameRealization) :=
  eqToIso ((congrArg (fun F ↦ F.obj m)
    (Functor.curry_obj_uncurry_obj JTRelativeReedyFrame.GammaOuter)).symm) ≪≫
      fixedRepresentedFreeNatIso JTFrameAdjunction.frameRealization
        JTFrameAdjunction.frameParameter frameRepresentedPairIso m

/-- The actual Xi frame is the represented restriction of its free-weight realization. -/
def xiFreeRepresentation (m : ReverseSimplex) :
    xiVertical m ≅
      SSet.stdSimplex ⋙
        (outerFree m ⋙
          (DaggerJTRealization.daggerRealization ⋙
            OrdinaryRigidification.DaggerRigidification.daggerRigidification)) :=
  fixedRepresentedFreeNatIso
    (DaggerJTRealization.daggerRealization ⋙
      OrdinaryRigidification.DaggerRigidification.daggerRigidification)
    RigidifiedJTFrames.Xi xiRepresentedPairIso m

/-- The uniquely normalized all-weight identification of actual free Gamma realization. -/
def gammaFreeWeightedIso (m : ReverseSimplex) :
    outerFree m ⋙ JTFrameAdjunction.frameRealization ≅ gammaWeighted m := by
  letI : PreservesColimitsOfSize.{0, 0}
      (outerFree m ⋙ JTFrameAdjunction.frameRealization) :=
    (gammaFreeAdjunction m).leftAdjoint_preservesColimits
  exact Presheaf.uniqueExtensionAlongULiftYoneda
    (outerFree m ⋙ JTFrameAdjunction.frameRealization)
    (gammaFreeRepresentation m)

/-- The uniquely normalized all-weight identification of actual free Xi realization. -/
def xiFreeWeightedIso (m : ReverseSimplex) :
    outerFree m ⋙
      (DaggerJTRealization.daggerRealization ⋙
        OrdinaryRigidification.DaggerRigidification.daggerRigidification) ≅
      xiWeighted m := by
  letI : PreservesColimitsOfSize.{0, 0}
      (outerFree m ⋙
        (DaggerJTRealization.daggerRealization ⋙
          OrdinaryRigidification.DaggerRigidification.daggerRigidification)) :=
    (xiFreeAdjunction m).leftAdjoint_preservesColimits
  exact Presheaf.uniqueExtensionAlongULiftYoneda
    (outerFree m ⋙
      (DaggerJTRealization.daggerRealization ⋙
        OrdinaryRigidification.DaggerRigidification.daggerRigidification))
    (xiFreeRepresentation m)

/-- The actual capital comparison evaluated on one outer free weight. -/
def actualFreeComparison (m : ReverseSimplex) :
    outerFree m ⋙ JTFrameAdjunction.frameRealization ⟶
      outerFree m ⋙
        (DaggerJTRealization.daggerRealization ⋙
          OrdinaryRigidification.DaggerRigidification.daggerRigidification) :=
  Functor.whiskerLeft (outerFree m) JTCoendComparison.comparison

/-- The constructed frame maps canonically into the realization of a free simplex weight. -/
def gammaRepresentedFreeIso (m : ReverseSimplex) (k : SimplexCategory) :
    (JTRelativeReedyFrame.GammaOuter.obj m).obj k ≅
      (outerFree m ⋙ JTFrameAdjunction.frameRealization).obj
        (SSet.stdSimplex.obj k) :=
  JTCoendMateFormula.frameGeneratorIso (m, k) ≪≫
    JTFrameAdjunction.frameRealization.mapIso (representedInputFreeIso m k)

/-- The literal Xi frame maps canonically into the target realization of a free simplex. -/
def xiRepresentedFreeIso (m : ReverseSimplex) (k : SimplexCategory) :
    (xiVertical m).obj k ≅
      (outerFree m ⋙
        (DaggerJTRealization.daggerRealization ⋙
          OrdinaryRigidification.DaggerRigidification.daggerRigidification)).obj
        (SSet.stdSimplex.obj k) :=
  (DaggerJTRealization.daggerRealization ⋙
    OrdinaryRigidification.DaggerRigidification.daggerRigidification).mapIso
      (representedInputFreeIso m k)

private theorem frameRepresentedPairIso_hom_app
    (m : ReverseSimplex) (k : SimplexCategory) :
    (frameRepresentedPairIso.app (m, k)).hom =
      JTCoendMateFormula.frameGenerator (m, k) := by
  rfl

private theorem xiRepresentedPairIso_hom_app
    (m : ReverseSimplex) (k : SimplexCategory) :
    (xiRepresentedPairIso.app (m, k)).hom =
      𝟙 (RigidifiedJTFrames.Xi.obj (m, k)) := by
  simp [xiRepresentedPairIso, RigidifiedJTFrames.Xi, DaggerJTAdjunction.frame,
    DaggerJTAdjunction.presheafRealization]

private theorem gammaFreeRepresentation_hom_app
    (m : ReverseSimplex) (k : SimplexCategory) :
    ((gammaFreeRepresentation m).app k).hom = (gammaRepresentedFreeIso m k).hom := by
  simp [gammaFreeRepresentation, fixedRepresentedFreeNatIso,
    gammaRepresentedFreeIso]
  change (frameRepresentedPairIso.app (m, k)).hom ≫
    JTFrameAdjunction.frameRealization.map (representedInputFreeIso m k).hom = _
  rw [frameRepresentedPairIso_hom_app]
  rfl

private theorem xiFreeRepresentation_hom_app
    (m : ReverseSimplex) (k : SimplexCategory) :
    ((xiFreeRepresentation m).app k).hom = (xiRepresentedFreeIso m k).hom := by
  simp [xiFreeRepresentation, fixedRepresentedFreeNatIso,
    xiRepresentedFreeIso]
  change (xiRepresentedPairIso.app (m, k)).hom ≫
    (DaggerJTRealization.daggerRealization ⋙
      OrdinaryRigidification.DaggerRigidification.daggerRigidification).map
        (representedInputFreeIso m k).hom = _
  rw [xiRepresentedPairIso_hom_app]
  simp

private theorem gammaFreeWeightedIso_fac (m : ReverseSimplex) (k : SimplexCategory) :
    ((gammaFreeRepresentation m).app k).hom ≫
      (gammaFreeWeightedIso m).hom.app (SSet.stdSimplex.obj k) =
        (uliftYoneda.{0}.leftKanExtensionUnit
          (JTRelativeReedyFrame.GammaOuter.obj m)).app k := by
  letI : PreservesColimitsOfSize.{0, 0}
      (outerFree m ⋙ JTFrameAdjunction.frameRealization) :=
    (gammaFreeAdjunction m).leftAdjoint_preservesColimits
  letI : (outerFree m ⋙ JTFrameAdjunction.frameRealization).IsLeftKanExtension
      (gammaFreeRepresentation m).hom :=
    Presheaf.isLeftKanExtension_of_preservesColimits _ (gammaFreeRepresentation m)
  have h := Functor.descOfIsLeftKanExtension_fac
    (outerFree m ⋙ JTFrameAdjunction.frameRealization)
    (gammaFreeRepresentation m).hom (gammaWeighted m)
    (uliftYoneda.{0}.leftKanExtensionUnit
      (JTRelativeReedyFrame.GammaOuter.obj m))
  have hk := NatTrans.congr_app h k
  change ((gammaFreeRepresentation m).app k).hom ≫
    (gammaFreeWeightedIso m).hom.app (SSet.stdSimplex.obj k) =
      (uliftYoneda.{0}.leftKanExtensionUnit
        (JTRelativeReedyFrame.GammaOuter.obj m)).app k at hk
  exact hk

private theorem xiFreeWeightedIso_fac (m : ReverseSimplex) (k : SimplexCategory) :
    ((xiFreeRepresentation m).app k).hom ≫
      (xiFreeWeightedIso m).hom.app (SSet.stdSimplex.obj k) =
        (uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m)).app k := by
  letI : PreservesColimitsOfSize.{0, 0}
      (outerFree m ⋙
        (DaggerJTRealization.daggerRealization ⋙
          OrdinaryRigidification.DaggerRigidification.daggerRigidification)) :=
    (xiFreeAdjunction m).leftAdjoint_preservesColimits
  letI : (outerFree m ⋙
      (DaggerJTRealization.daggerRealization ⋙
        OrdinaryRigidification.DaggerRigidification.daggerRigidification)).IsLeftKanExtension
      (xiFreeRepresentation m).hom :=
    Presheaf.isLeftKanExtension_of_preservesColimits _ (xiFreeRepresentation m)
  have h := Functor.descOfIsLeftKanExtension_fac
    (outerFree m ⋙
      (DaggerJTRealization.daggerRealization ⋙
        OrdinaryRigidification.DaggerRigidification.daggerRigidification))
    (xiFreeRepresentation m).hom (xiWeighted m)
    (uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m))
  have hk := NatTrans.congr_app h k
  change ((xiFreeRepresentation m).app k).hom ≫
    (xiFreeWeightedIso m).hom.app (SSet.stdSimplex.obj k) =
      (uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m)).app k at hk
  exact hk

/-- On a free represented simplex the capital comparison is literally the
original Gamma-to-Xi frame comparison under the canonical generator isomorphisms. -/
theorem actualFreeComparison_represented (m : ReverseSimplex) (k : SimplexCategory) :
    (gammaRepresentedFreeIso m k).hom ≫
      (actualFreeComparison m).app (SSet.stdSimplex.obj k) =
      JTCoendComparison.parameterComparison.app (m, k) ≫
        (xiRepresentedFreeIso m k).hom := by
  dsimp only [gammaRepresentedFreeIso, xiRepresentedFreeIso, actualFreeComparison,
    Iso.trans_hom, Functor.mapIso_hom, Functor.whiskerLeft_app]
  rw [Category.assoc, JTCoendComparison.comparison.naturality,
    ← Category.assoc]
  change (JTCoendMateFormula.frameGenerator (m, k) ≫
    JTCoendComparison.comparison.app (JTCoendMateFormula.representedInput (m, k))) ≫
      _ = _
  rw [JTCoendMateFormula.frameGenerator_comparison]

/-- The literal original comparison with one outer reversal index fixed. -/
def verticalComparison (m : ReverseSimplex) :
    JTRelativeReedyFrame.GammaOuter.obj m ⟶ xiVertical m where
  app k := JTCoendComparison.parameterComparison.app (m, k)
  naturality := by
    intro k l f
    have h := JTCoendComparison.parameterComparison.naturality
      (show (m, k) ⟶ (m, l) from (𝟙 m, f))
    rw [JTFrameAdjunction.frameParameter_vertical_map] at h
    change (JTRelativeReedyFrame.GammaOuter.obj m).map f ≫
      JTCoendComparison.parameterComparison.app (m, l) =
        JTCoendComparison.parameterComparison.app (m, k) ≫
          RigidifiedJTFrames.Xi.map (𝟙 m, f)
    exact h

private local instance (m : ReverseSimplex) :
    (gammaWeighted m).IsLeftKanExtension
      (uliftYoneda.{0}.leftKanExtensionUnit
        (JTRelativeReedyFrame.GammaOuter.obj m)) := by
  dsimp [gammaWeighted]
  infer_instance

/-- The independently induced all-weight comparison from the literal Gamma-to-Xi map. -/
def weightedComparison (m : ReverseSimplex) : gammaWeighted m ⟶ xiWeighted m :=
  (gammaWeighted m).descOfIsLeftKanExtension
    (uliftYoneda.{0}.leftKanExtensionUnit
      (JTRelativeReedyFrame.GammaOuter.obj m))
    (xiWeighted m)
    (verticalComparison m ≫
      uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m))

/-- On every represented vertical weight the comparison is exactly the
original frame map, followed by the native Xi Yoneda unit. -/
theorem weightedComparison_fac (m : ReverseSimplex) (k : SimplexCategory) :
    (uliftYoneda.{0}.leftKanExtensionUnit
      (JTRelativeReedyFrame.GammaOuter.obj m)).app k ≫
        (weightedComparison m).app (uliftYoneda.{0}.obj k) =
      (verticalComparison m).app k ≫
        (uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m)).app k := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app
      (Functor.descOfIsLeftKanExtension_fac
        (gammaWeighted m)
        (uliftYoneda.{0}.leftKanExtensionUnit
          (JTRelativeReedyFrame.GammaOuter.obj m))
        (xiWeighted m)
        (verticalComparison m ≫
          uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m))) k

/-- For every simplicial-set weight, the actual capital Lambda is the unique
weighted comparison induced by the literal original Gamma-to-Xi frame map. -/
theorem actualFreeComparison_weighted (m : ReverseSimplex) :
    actualFreeComparison m ≫ (xiFreeWeightedIso m).hom =
      (gammaFreeWeightedIso m).hom ≫ weightedComparison m := by
  letI : PreservesColimitsOfSize.{0, 0}
      (outerFree m ⋙ JTFrameAdjunction.frameRealization) :=
    (gammaFreeAdjunction m).leftAdjoint_preservesColimits
  letI : (outerFree m ⋙ JTFrameAdjunction.frameRealization).IsLeftKanExtension
      (gammaFreeRepresentation m).hom :=
    Presheaf.isLeftKanExtension_of_preservesColimits _ (gammaFreeRepresentation m)
  apply Functor.hom_ext_of_isLeftKanExtension
    (outerFree m ⋙ JTFrameAdjunction.frameRealization)
    (gammaFreeRepresentation m).hom
  apply NatTrans.ext
  funext k
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  have hRep : ((gammaFreeRepresentation m).app k).hom ≫
      (actualFreeComparison m).app (SSet.stdSimplex.obj k) =
        (verticalComparison m).app k ≫ ((xiFreeRepresentation m).app k).hom := by
    simpa only [gammaFreeRepresentation_hom_app, xiFreeRepresentation_hom_app,
      verticalComparison] using actualFreeComparison_represented m k
  calc
    ((gammaFreeRepresentation m).app k).hom ≫
        (actualFreeComparison m).app (SSet.stdSimplex.obj k) ≫
          (xiFreeWeightedIso m).hom.app (SSet.stdSimplex.obj k) =
      (verticalComparison m).app k ≫
        ((xiFreeRepresentation m).app k).hom ≫
          (xiFreeWeightedIso m).hom.app (SSet.stdSimplex.obj k) := by
            rw [← Category.assoc, hRep, Category.assoc]
    _ = (verticalComparison m).app k ≫
        (uliftYoneda.{0}.leftKanExtensionUnit (xiVertical m)).app k := by
          rw [xiFreeWeightedIso_fac]
    _ = (uliftYoneda.{0}.leftKanExtensionUnit
        (JTRelativeReedyFrame.GammaOuter.obj m)).app k ≫
          (weightedComparison m).app (SSet.stdSimplex.obj k) :=
            (weightedComparison_fac m k).symm
    _ = ((gammaFreeRepresentation m).app k).hom ≫
        (gammaFreeWeightedIso m).hom.app (SSet.stdSimplex.obj k) ≫
          (weightedComparison m).app (SSet.stdSimplex.obj k) := by
            rw [← Category.assoc, gammaFreeWeightedIso_fac]

end

end DaggerModels.PartII.JTProjectiveGeneratorRealization
