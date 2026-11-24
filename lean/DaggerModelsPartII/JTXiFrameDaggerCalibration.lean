import DaggerModelsPartII.JTRealizationBoxCalibration
import DaggerModelsPartII.JTParameterReversal

/-!
# Dagger calibration of the represented JT frame

The ordinary external-box comparison is tested on actual coend generators.
The horizontal reversal and groupoid inversion then give the dagger square.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTXiFrameDaggerCalibration

open DaggerJTAdjunction DaggerJTFrameUnderlying DaggerJTRepresentedFrames
open JTRealizationBoxCalibration JTRealizationBox OrdinaryJTRealization
open JTRealizationGenerators JTRealizationVertices JTReversalInput
open GroupoidSimplexReversal JTParameterReversal

noncomputable section

/-- The product dagger on the literal ordinary parameter of the
represented dagger JT frame. -/
def productDaggerIso (p : DaggerIndex) :
    frameParameter.obj p ≅ (frameParameter.obj p).op :=
  tensorIso
    (DaggerSSet.daggerIso (reversalSimplex.obj p.1))
    (DaggerSSet.daggerIso (daggerParameter.obj p.2))

/-- Yoneda evaluation commutes with reversal of a represented dagger simplex. -/
theorem yoneda_dagger (X : DaggerSSet.{0}) (m : SimplexCategory)
    (x : X.toSSet.obj (Opposite.op m)) :
    SSet.yonedaEquiv.symm x ≫ X.dagger =
      (DaggerOriginalStandardSimplexReversal.standardSimplexReversalIso m.len).symm.hom ≫
        SSet.opFunctor.map (SSet.yonedaEquiv.symm
          (SSet.opObjEquiv (X.dagger.app (Opposite.op m) x))) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  simp [SSet.yonedaEquiv, uliftYonedaEquiv,
    DaggerOriginalStandardSimplexReversal.standardSimplexReversalIso,
    DaggerOriginalStandardSimplexReversal.standardSimplexReversalInv,
    SSet.opFunctor_map]
  change X.dagger.app (Opposite.op m) x =
    X.toSSet.map (SimplexCategory.rev.map (𝟙 m)).op
      (X.dagger.app (Opposite.op m) x)
  simp

/-- The product formula reverses the represented Yoneda simplex and the
groupoid parameter independently, with the literal parameter inversion. -/
theorem product_generator_dagger (p : DaggerIndex)
    (m l : SimplexCategory)
    (x : (underlyingSimplex.obj p.1).obj (Opposite.op m))
    (f : l ⟶ p.2) :
    (SSet.yonedaEquiv.symm x ⊗ₘ GroupoidSimplex.parameter.map f) ≫
        (productDaggerIso p).hom =
      (tReversalIso.hom.app (m, l)) ≫
        SSet.opFunctor.map
          (SSet.yonedaEquiv.symm
            (SSet.opObjEquiv
              ((reversalSimplex.obj p.1).dagger.app (Opposite.op m) x)) ⊗ₘ
            GroupoidSimplex.parameter.map f) := by
  change (SSet.yonedaEquiv.symm x ⊗ₘ GroupoidSimplex.parameter.map f) ≫
      ((reversalSimplex.obj p.1).dagger ⊗ₘ
        (daggerParameter.obj p.2).dagger) =
    ((DaggerOriginalStandardSimplexReversal.standardSimplexReversalIso m.len).symm.hom ⊗ₘ
      (daggerParameter.obj l).dagger) ≫
      (SSet.opFunctor.map (SSet.yonedaEquiv.symm
        (SSet.opObjEquiv
          ((reversalSimplex.obj p.1).dagger.app (Opposite.op m) x))) ⊗ₘ
        SSet.opFunctor.map (GroupoidSimplex.parameter.map f))
  simp only [tensorHom_comp_tensorHom]
  exact congrArg₂ (fun a b => a ⊗ₘ b)
    (yoneda_dagger (reversalSimplex.obj p.1) m x)
    ((daggerParameter.map f).comm)

/-- The represented-frame ordinary comparison on one actual coend
generator; the represented ordinary box is literally the same presheaf. -/
private theorem representedBoxUnderlyingIso_generator (p : DaggerIndex)
    (m l : SimplexCategory)
    (x : (underlyingSimplex.obj p.1).obj (Opposite.op m))
    (β : (SSet.stdSimplex.obj p.2).obj (Opposite.op l)) :
    generator (ordinaryInput.obj (representedTensorPair.obj p))
        (m, l) (x, β) ≫ (representedBoxUnderlyingIso p).hom =
      SSet.yonedaEquiv.symm x ⊗ₘ
        GroupoidSimplex.parameter.map (SSet.stdSimplex.objEquiv β) := by
  simpa [representedBoxUnderlyingIso, representedOrdinaryBoxIso] using
    realizationBoxIso_generator
      (underlyingSimplex.obj p.1) p.2 m l x β

private theorem representedBox_dagger_generator (p : DaggerIndex)
    (m l : SimplexCategory)
    (x : (underlyingSimplex.obj p.1).obj (Opposite.op m))
    (β : (SSet.stdSimplex.obj p.2).obj (Opposite.op l)) :
    generator (ordinaryInput.obj (representedTensorPair.obj p)) (m, l) (x, β) ≫
        (representedBoxUnderlyingIso p).hom ≫ (productDaggerIso p).hom =
      generator (ordinaryInput.obj (representedTensorPair.obj p)) (m, l) (x, β) ≫
        (DaggerJTRealization.daggerRealization.obj
          (representedTensorPair.obj p)).dagger ≫
          SSet.opFunctor.map (representedBoxUnderlyingIso p).hom := by
  let f : l ⟶ p.2 := SSet.stdSimplex.objEquiv β
  let xd := SSet.opObjEquiv
    ((reversalSimplex.obj p.1).dagger.app (Opposite.op m) x)
  have hd := DaggerJTRealization.generator_toOpposite
    (representedTensorPair.obj p) (m, l) (x, β)
  simp only [JTSimplexReversal.horizontalIso_hom_app] at hd
  change generator (ordinaryInput.obj (representedTensorPair.obj p))
      (m, l) (x, β) ≫
        (DaggerJTRealization.daggerRealization.obj
          (representedTensorPair.obj p)).dagger =
      tReversalIso.hom.app (m, l) ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj (representedTensorPair.obj p))
          (m, l) (xd, β)) at hd
  calc
    _ = (SSet.yonedaEquiv.symm x ⊗ₘ GroupoidSimplex.parameter.map f) ≫
          (productDaggerIso p).hom := by
          rw [← Category.assoc, representedBoxUnderlyingIso_generator]
    _ = tReversalIso.hom.app (m, l) ≫
          SSet.opFunctor.map
            (SSet.yonedaEquiv.symm xd ⊗ₘ GroupoidSimplex.parameter.map f) :=
      product_generator_dagger p m l x f
    _ = tReversalIso.hom.app (m, l) ≫ SSet.opFunctor.map
          (generator (ordinaryInput.obj (representedTensorPair.obj p))
            (m, l) (xd, β) ≫ (representedBoxUnderlyingIso p).hom) := by
          rw [representedBoxUnderlyingIso_generator]
          rfl
    _ = _ := by
          rw [Functor.map_comp]
          exact congrArg
            (fun q ↦ q ≫ SSet.opFunctor.map (representedBoxUnderlyingIso p).hom)
            hd.symm

/-- The ordinary product comparison for the represented JT frame
intertwines the actual coend dagger and both factors of the product dagger. -/
theorem representedBox_dagger (p : DaggerIndex) :
    (representedBoxUnderlyingIso p).hom ≫ (productDaggerIso p).hom =
      (DaggerJTRealization.daggerRealization.obj
        (representedTensorPair.obj p)).dagger ≫
        SSet.opFunctor.map (representedBoxUnderlyingIso p).hom := by
  apply (simplexCoconeIsColimit
    (ordinaryInput.obj (representedTensorPair.obj p))).hom_ext
  intro σ
  let w := uliftYonedaEquiv.{0} σ.hom
  have h := representedBox_dagger_generator p σ.left.1 σ.left.2 w.1 w.2
  have hg : generator (ordinaryInput.obj (representedTensorPair.obj p))
      (σ.left.1, σ.left.2) (w.1, w.2) =
        (simplexCocone (ordinaryInput.obj (representedTensorPair.obj p))).ι.app σ := by
    change generator (ordinaryInput.obj (representedTensorPair.obj p)) σ.left
      (uliftYonedaEquiv.{0} σ.hom) = _
    simp only [generator, simplexCocone_leg, Equiv.symm_apply_apply]
  rw [hg] at h
  exact h

/-- The chosen frame comparison is the dagger represented-frame map followed
by the ordinary represented-box comparison. -/
private theorem frameUnderlyingIso_hom (p : DaggerIndex) :
    (frameUnderlyingIso.app p).hom =
      (frameRepresentation.app p).hom.hom ≫
        (representedBoxUnderlyingIso p).hom := by
  rfl

/-- The actual represented JT frame comparison intertwines its specified
dagger with horizontal simplex reversal and groupoid inversion. -/
theorem frameUnderlyingIso_dagger (p : DaggerIndex) :
    (frameUnderlyingIso.app p).hom ≫ (productDaggerIso p).hom =
      (frame.obj p).dagger ≫
        SSet.opFunctor.map (frameUnderlyingIso.app p).hom := by
  rw [frameUnderlyingIso_hom, Functor.map_comp]
  calc
    _ = (frameRepresentation.app p).hom.hom ≫
          ((representedBoxUnderlyingIso p).hom ≫ (productDaggerIso p).hom) := by
            rw [Category.assoc]
    _ = (frameRepresentation.app p).hom.hom ≫
          ((DaggerJTRealization.daggerRealization.obj
            (representedTensorPair.obj p)).dagger ≫
              SSet.opFunctor.map (representedBoxUnderlyingIso p).hom) := by
            rw [representedBox_dagger]
    _ = ((frameRepresentation.app p).hom.hom ≫
          (DaggerJTRealization.daggerRealization.obj
            (representedTensorPair.obj p)).dagger) ≫
              SSet.opFunctor.map (representedBoxUnderlyingIso p).hom := by
            rw [Category.assoc]
    _ = ((frame.obj p).dagger ≫
          SSet.opFunctor.map (frameRepresentation.app p).hom.hom) ≫
              SSet.opFunctor.map (representedBoxUnderlyingIso p).hom := by
            have hc :
                (frameRepresentation.app p).hom.hom ≫
                    (DaggerJTRealization.daggerRealization.obj
                      (representedTensorPair.obj p)).dagger =
                  (frame.obj p).dagger ≫
                    SSet.opFunctor.map (frameRepresentation.app p).hom.hom :=
              (frameRepresentation.app p).hom.comm
            exact congrArg
              (fun q ↦ q ≫ SSet.opFunctor.map (representedBoxUnderlyingIso p).hom)
              hc
    _ = _ := by
          rw [Category.assoc]

end

end DaggerModels.PartII.JTXiFrameDaggerCalibration
