import DaggerModelsPartII.JTStrictificationCoefficients
import DaggerModelsPartII.JTActualCosimplicialFrame
import DaggerModelsPartII.JTZeroObjects
import DaggerModelsPartII.JTEndpointObjects
import DaggerModelsPartII.JTRawVertexRecovery
import DaggerModelsPartII.JTRawFreeInnerComparison
import DaggerModels.RigidificationVertices
import DaggerModelsPartII.JTCoendMateFormula
import DaggerModelsPartII.JTFrameGeneratorCalibration

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModels.OrdinaryRigidification

namespace DaggerModels.PartII.JTChosenPsiVertices

open JTStrictificationCoefficients JTFrameAdjunction JTZeroObjects

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- Raw JT zero vertices are natural for the literal coend realization. -/
theorem zeroVertex_map {P Q : OrdinaryJTRealization.BiPresheaf} (f : P ⟶ Q)
    (x : P.obj (op (⦋0⦌, ⦋0⦌))) :
    (OrdinaryJTRealization.realization.map f).app (op ⦋0⦌)
        (JTRawVertexRecovery.zeroVertex P x) =
      JTRawVertexRecovery.zeroVertex Q (f.app (op (⦋0⦌, ⦋0⦌)) x) := by
  change SSet.yonedaEquiv
    ((JTGtildeOrderedFiberAction.zeroTensorVertex ≫
      JTRealizationGenerators.generator P (⦋0⦌, ⦋0⦌) x) ≫
        OrdinaryJTRealization.realization.map f) = _
  rw [Category.assoc, JTRealizationGenerators.generator_naturality]
  rfl

/-- Evaluation of any literal frame adjoint on a represented generator. -/
theorem frameAdjoint_generator (W : Source) (C : DaggerSimplicialCat.{0, 0})
    (a : frameRealization.obj W ⟶ C) (p : DaggerJTAdjunction.DaggerIndex)
    (x : (W.obj (op p.1)).obj (op p.2)) :
    ((adjunction.homEquiv W C a).app (op p.1)).app (op p.2) x =
      JTCoendMateFormula.frameGeneratorEquiv C p
        (JTCoendMateFormula.frameGenerator p ≫
          frameRealization.map
            ((JTCoendMateFormula.representedEvaluation W p).symm x) ≫ a) := by
  let u := (JTCoendMateFormula.representedEvaluation W p).symm x
  have h := JTCoendMateFormula.representedEvaluation_naturality p u
    (adjunction.homEquiv W C a)
  rw [Equiv.apply_symm_apply] at h
  rw [← adjunction.homEquiv_naturality_left u a] at h
  change _ = JTCoendMateFormula.representedEvaluation (frameNerve.obj C) p
    (adjunction.homEquiv (JTCoendMateFormula.representedInput p) C
      ((JTCoendMateFormula.frameGeneratorIso p).inv ≫
        (JTCoendMateFormula.frameGenerator p ≫ frameRealization.map u ≫ a)))
  have hcancel : (JTCoendMateFormula.frameGeneratorIso p).inv ≫
      JTCoendMateFormula.frameGenerator p = 𝟙 _ :=
    Iso.inv_hom_id (JTCoendMateFormula.frameGeneratorIso p)
  simp only [← Category.assoc, hcancel, Category.id_comp]
  exact h.symm

/-- The literal represented zero-frame Hom obtained from chosenPsi's
specified coefficient map. -/
def chosenPsiZeroHom (W : Source)
    (x : ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌)) :
    JTFrameAdjunction.frameParameter.obj (zeroIndex, ⦋0⦌) ⟶
      rigidCoefficient (chosenT W) :=
  JTCoendMateFormula.frameGenerator (zeroIndex, ⦋0⦌) ≫
    frameRealization.map
      ((JTCoendMateFormula.representedEvaluation (JTStrictificationMaps.Qproj.obj W)
        (zeroIndex, ⦋0⦌)).symm x) ≫
      (JTCoendComparison.comparison.app (JTStrictificationMaps.Qproj.obj W) ≫
        chosenA W)

/-- The original chosenPsi zero component is the literal represented
zero-frame Hom once the canonical Gamma generator is calibrated. -/
theorem chosenPsi_zero_hom_of_gamma (W : Source)
    (hΓ : ∀ f : JTFrameAdjunction.frameParameter.obj (zeroIndex, ⦋0⦌) ⟶
      rigidCoefficient (chosenT W),
        JTCoendMateFormula.frameGeneratorEquiv
          (rigidCoefficient (chosenT W)) (zeroIndex, ⦋0⦌) f = f)
    (x : ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌)) :
    (((chosenPsi W).app (op zeroIndex)).app (op ⦋0⦌)) x =
      chosenPsiZeroHom W x := by
  let b := JTCoendComparison.comparison.app (JTStrictificationMaps.Qproj.obj W) ≫
    chosenA W
  have hψ : chosenPsi W = adjunction.homEquiv
      (JTStrictificationMaps.Qproj.obj W) (rigidCoefficient (chosenT W)) b := by
    change JTStrictificationMaps.psi W (chosenG W)
      (JTObjectPreservingReplacement.r
        (OrdinaryRigidification.DaggerRigidification.daggerRigidification.obj
          (chosenT W))) = _
    simp only [JTStrictificationMaps.psi, Adjunction.homEquiv_unit]
    rfl
  rw [hψ]
  have h := frameAdjoint_generator (JTStrictificationMaps.Qproj.obj W)
    (rigidCoefficient (chosenT W)) b (zeroIndex, ⦋0⦌) x
  change _ = JTCoendMateFormula.frameGeneratorEquiv
    (rigidCoefficient (chosenT W)) (zeroIndex, ⦋0⦌) (chosenPsiZeroHom W x) at h
  exact h.trans (hΓ _)

/-- At degree zero, the literal Gamma-to-Xi comparison is the identity;
the zero Hom is the rigidified represented source map followed by chosenA. -/
theorem chosenPsiZeroHom_eq (W : Source)
    (x : ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌)) :
    chosenPsiZeroHom W x =
      OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map
          ((JTCoendMateFormula.representedEvaluation (JTStrictificationMaps.Qproj.obj W)
            (zeroIndex, ⦋0⦌)).symm x)) ≫ chosenA W := by
  let u := (JTCoendMateFormula.representedEvaluation
    (JTStrictificationMaps.Qproj.obj W) (zeroIndex, ⦋0⦌)).symm x
  calc
    chosenPsiZeroHom W x =
        JTCoendMateFormula.frameGenerator (zeroIndex, ⦋0⦌) ≫
          (JTFrameAdjunction.frameRealization.map u ≫
            JTCoendComparison.comparison.app (JTStrictificationMaps.Qproj.obj W)) ≫
              chosenA W := by
                rfl
    _ = JTCoendMateFormula.frameGenerator (zeroIndex, ⦋0⦌) ≫
          (JTCoendComparison.comparison.app
            (JTCoendMateFormula.representedInput (zeroIndex, ⦋0⦌)) ≫
              OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
                (DaggerJTRealization.daggerRealization.map u)) ≫ chosenA W := by
                rw [JTCoendComparison.comparison_naturality u]
    _ = JTCoendComparison.parameterComparison.app (zeroIndex, ⦋0⦌) ≫
          OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
            (DaggerJTRealization.daggerRealization.map u) ≫ chosenA W := by
                simp only [← Category.assoc,
                  JTCoendMateFormula.frameGenerator_comparison]
    _ = _ := by
      rw [JTCoendComparison.parameterComparison_zero]
      change (𝟙 _ ≫
        OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
          (DaggerJTRealization.daggerRealization.map u)) ≫ chosenA W = _
      rw [Category.id_comp]

/-- The rigidified zero Xi frame has exactly one object. -/
private theorem xiZeroObj_subsingleton :
    Subsingleton (RigidifiedJTFrames.Xi.obj (zeroIndex, ⦋0⦌)).Obj := by
  let e : RigidifiedJTFrames.Xi.obj (zeroIndex, ⦋0⦌) ≅
      DaggerDiscreteObjects.point.{0, 0} :=
    (RigidifiedJTFrames.XiZeroIso.app zeroIndex) ≪≫
      JTEndpointObjects.zeroPointIso
  have hp : Subsingleton DaggerDiscreteObjects.point.{0, 0}.Obj := by
    change Subsingleton PUnit.{1}
    infer_instance
  constructor
  intro x y
  have h : e.hom.obj x = e.hom.obj y := hp.elim _ _
  have h' := congrArg e.inv.obj h
  change (e.hom ≫ e.inv).obj x = (e.hom ≫ e.inv).obj y at h'
  rw [Iso.hom_inv_id] at h'
  exact h'

/-- Both canonical zero-generator descriptions select the unique object
of the actual Xi zero frame. -/
private theorem xiZeroObject_rawVertex :
    ((RigidifiedJTFrames.XiZeroIso.app zeroIndex).inv).obj zeroObject =
      RigidificationVertices.vertexEquiv
        (DaggerJTAdjunction.frame.obj (zeroIndex, ⦋0⦌)).toSSet
        (JTRawVertexRecovery.zeroVertexEquiv
          (JTReversalInput.ordinaryInput.obj
            (JTCoendMateFormula.representedInput (zeroIndex, ⦋0⦌)))
          (JTCoendMateFormula.representedEvaluation
            (JTCoendMateFormula.representedInput (zeroIndex, ⦋0⦌))
              (zeroIndex, ⦋0⦌) (𝟙 _))) := by
  letI : Subsingleton (RigidifiedJTFrames.Xi.obj (zeroIndex, ⦋0⦌)).Obj :=
    xiZeroObj_subsingleton
  haveI : Subsingleton
      ((JTFrameZero.zeroSection ⋙ RigidifiedJTFrames.Xi).obj zeroIndex).Obj := by
    change Subsingleton (RigidifiedJTFrames.Xi.obj (zeroIndex, ⦋0⦌)).Obj
    exact xiZeroObj_subsingleton
  exact Subsingleton.elim _ _

/-- The actual zero component of the frame nerve classifies target objects. -/
def frameZeroVertexEquiv (C : DaggerSimplicialCat.{0, 0}) :
    ((frameNerve.obj C).obj (op zeroIndex)).obj (op ⦋0⦌) ≃ C.Obj := by
  change ((JTRelativeReedyFrame.GammaOuter.obj zeroIndex).obj ⦋0⦌ ⟶ C) ≃ C.Obj
  exact (JTActualCosimplicialFrame.GammaZeroIso.app zeroIndex).homCongr
    (Iso.refl C) |>.trans (zeroHomEquiv C)

/-- The original source zero component is exactly the raw realization vertex set. -/
def sourceRawVertexEquiv (W : Source) :
    ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌) ≃
      (OrdinaryJTRealization.realization.obj
        (JTReversalInput.ordinaryInput.obj (JTStrictificationMaps.Qproj.obj W))).obj
          (op ⦋0⦌) := by
  exact JTRawVertexRecovery.zeroVertexEquiv
    (JTReversalInput.ordinaryInput.obj (JTStrictificationMaps.Qproj.obj W))

/-- The represented zero coefficient maps to the exact source coefficient;
the original raw coend vertex follows by generator naturality. -/
theorem representedRawZeroVertex_map (W : Source)
    (x : ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌)) :
    let U := JTCoendMateFormula.representedInput (zeroIndex, ⦋0⦌)
    let u := (JTCoendMateFormula.representedEvaluation
      (JTStrictificationMaps.Qproj.obj W) (zeroIndex, ⦋0⦌)).symm x
    let z := JTCoendMateFormula.representedEvaluation U (zeroIndex, ⦋0⦌) (𝟙 U)
    (DaggerJTRealization.daggerRealization.map u).hom.app (op ⦋0⦌)
        (JTRawVertexRecovery.zeroVertex (JTReversalInput.ordinaryInput.obj U) z) =
      sourceRawVertexEquiv W x := by
  dsimp only
  let U := JTCoendMateFormula.representedInput (zeroIndex, ⦋0⦌)
  let u := (JTCoendMateFormula.representedEvaluation
    (JTStrictificationMaps.Qproj.obj W) (zeroIndex, ⦋0⦌)).symm x
  let z := JTCoendMateFormula.representedEvaluation U (zeroIndex, ⦋0⦌) (𝟙 U)
  have hz : ((JTReversalInput.ordinaryInput.map u).app (op (⦋0⦌, ⦋0⦌))) z = x := by
    have h := JTCoendMateFormula.representedEvaluation_naturality
      (zeroIndex, ⦋0⦌) (𝟙 U) u
    change ((u.app (op zeroIndex)).app (op ⦋0⦌)) z = x
    calc
      _ = JTCoendMateFormula.representedEvaluation
            (JTStrictificationMaps.Qproj.obj W) (zeroIndex, ⦋0⦌) (𝟙 U ≫ u) := h.symm
      _ = JTCoendMateFormula.representedEvaluation
            (JTStrictificationMaps.Qproj.obj W) (zeroIndex, ⦋0⦌) u := by
              rw [Category.id_comp]
      _ = x := Equiv.apply_symm_apply _ _
  change (OrdinaryJTRealization.realization.map (JTReversalInput.ordinaryInput.map u)).app
      (op ⦋0⦌) (JTRawVertexRecovery.zeroVertex
        (JTReversalInput.ordinaryInput.obj U) z) =
    JTRawVertexRecovery.zeroVertex
      (JTReversalInput.ordinaryInput.obj (JTStrictificationMaps.Qproj.obj W)) x
  rw [zeroVertex_map, hz]

/-- The expected strictification vertex map is a bijection, with the
chosen free-inner map as its only non-isomorphism factor. -/
def expectedVertexEquiv (W : Source) :
    ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌) ≃
      (rigidCoefficient (chosenT W)).Obj := by
  let e :
      (DaggerJTRealization.daggerRealization.obj
        (JTStrictificationMaps.Qproj.obj W)).toSSet.obj (op ⦋0⦌) ≃
        (chosenT W).toSSet.obj (op ⦋0⦌) :=
    Equiv.ofBijective ((chosenG W).hom.app (op ⦋0⦌))
      (JTRawFreeInnerComparison.chosenG_vertex_bijective W)
  exact (sourceRawVertexEquiv W).trans e |>.trans
    (RigidificationVertices.vertexEquiv (chosenT W).toSSet)

/-- The required point-set calibration for the literal chosen map. -/
def ChosenPsiZeroFormula (W : Source) : Prop :=
  ∀ x : ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌),
    frameZeroVertexEquiv (rigidCoefficient (chosenT W))
        (((chosenPsi W).app (op zeroIndex)).app (op ⦋0⦌) x) =
      expectedVertexEquiv W x

/-- The Gamma native calibration closes the exact original chosenPsi
vertex formula, using the unique object of the zero Xi frame. -/
theorem chosenPsiZeroFormula_of_gamma (W : Source)
    (hΓ : ∀ f : JTFrameAdjunction.frameParameter.obj (zeroIndex, ⦋0⦌) ⟶
      rigidCoefficient (chosenT W),
        JTCoendMateFormula.frameGeneratorEquiv
          (rigidCoefficient (chosenT W)) (zeroIndex, ⦋0⦌) f = f) :
    ChosenPsiZeroFormula W := by
  intro x
  rw [chosenPsi_zero_hom_of_gamma W hΓ x]
  let U := JTCoendMateFormula.representedInput (zeroIndex, ⦋0⦌)
  let u := (JTCoendMateFormula.representedEvaluation
    (JTStrictificationMaps.Qproj.obj W) (zeroIndex, ⦋0⦌)).symm x
  let z := JTCoendMateFormula.representedEvaluation U (zeroIndex, ⦋0⦌) (𝟙 U)
  change JTZeroObjects.zeroHomEquiv (rigidCoefficient (chosenT W))
      ((JTActualCosimplicialFrame.GammaZeroIso.app zeroIndex).inv ≫
        chosenPsiZeroHom W x) = expectedVertexEquiv W x
  rw [JTZeroObjects.zeroHomEquiv_eq_obj]
  rw [chosenPsiZeroHom_eq]
  change (chosenA W).obj
    ((OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
      (DaggerJTRealization.daggerRealization.map u)).obj
      ((RigidifiedJTFrames.XiZeroIso.app zeroIndex).inv.obj zeroObject)) =
        expectedVertexEquiv W x
  rw [xiZeroObject_rawVertex]
  have hraw := representedRawZeroVertex_map W x
  change (DaggerJTRealization.daggerRealization.map u).hom.app (op ⦋0⦌)
      (JTRawVertexRecovery.zeroVertex (JTReversalInput.ordinaryInput.obj U) z) =
    sourceRawVertexEquiv W x at hraw
  have hvert :
      (OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map u)).obj
          (RigidificationVertices.vertexEquiv
            (DaggerJTAdjunction.frame.obj (zeroIndex, ⦋0⦌)).toSSet
            (JTRawVertexRecovery.zeroVertex (JTReversalInput.ordinaryInput.obj U) z)) =
      RigidificationVertices.vertexEquiv
        (DaggerJTRealization.daggerRealization.obj
          (JTStrictificationMaps.Qproj.obj W)).toSSet
        ((DaggerJTRealization.daggerRealization.map u).hom.app (op ⦋0⦌)
          (JTRawVertexRecovery.zeroVertex (JTReversalInput.ordinaryInput.obj U) z)) :=
    RigidificationVertices.vertexEquiv_naturality _ _
  change (chosenA W).obj
    ((OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
      (DaggerJTRealization.daggerRealization.map u)).obj
        (RigidificationVertices.vertexEquiv
          (DaggerJTAdjunction.frame.obj (zeroIndex, ⦋0⦌)).toSSet
            (JTRawVertexRecovery.zeroVertex (JTReversalInput.ordinaryInput.obj U) z))) =
    expectedVertexEquiv W x
  rw [hvert]
  rw [hraw]
  rw [show chosenA W =
      OrdinaryRigidification.DaggerRigidification.daggerRigidification.map (chosenG W) ≫
        JTObjectPreservingReplacement.r
          (OrdinaryRigidification.DaggerRigidification.daggerRigidification.obj
            (chosenT W)) from rfl]
  change (JTObjectPreservingReplacement.r
      (OrdinaryRigidification.DaggerRigidification.daggerRigidification.obj
        (chosenT W))).obj
        ((OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
          (chosenG W)).obj
            (RigidificationVertices.vertexEquiv
              (DaggerJTRealization.daggerRealization.obj
                (JTStrictificationMaps.Qproj.obj W)).toSSet
              (sourceRawVertexEquiv W x))) = expectedVertexEquiv W x
  rw [JTObjectPreservingReplacement.r_obj]
  change (OrdinaryRigidification.rigidification.map (chosenG W).hom).obj
      (RigidificationVertices.vertexEquiv
        (DaggerJTRealization.daggerRealization.obj
          (JTStrictificationMaps.Qproj.obj W)).toSSet
        (sourceRawVertexEquiv W x)) = expectedVertexEquiv W x
  rw [RigidificationVertices.vertexEquiv_naturality]
  rfl

/-- Once the exact point-set calibration is supplied, the literal
strictification map is bijective on its original zero-row vertices. -/
theorem chosenPsi_zero_bijective_of_formula (W : Source)
    (h : ChosenPsiZeroFormula W) :
    Function.Bijective
      (((chosenPsi W).app (op zeroIndex)).app (op ⦋0⦌)) := by
  constructor
  · intro x y hxy
    apply (expectedVertexEquiv W).injective
    rw [← h x, ← h y, hxy]
  · intro z
    obtain ⟨x, hx⟩ := (expectedVertexEquiv W).surjective
      (frameZeroVertexEquiv (rigidCoefficient (chosenT W)) z)
    refine ⟨x, ?_⟩
    apply (frameZeroVertexEquiv (rigidCoefficient (chosenT W))).injective
    exact (h x).trans hx

/-- The exact chosen strictification map has the predicted zero-row
vertex action. -/
theorem chosenPsi_vertex_expected (W : Source)
    (x : ((JTStrictificationMaps.Qproj.obj W).obj (op zeroIndex)).obj (op ⦋0⦌)) :
    frameZeroVertexEquiv (rigidCoefficient (chosenT W))
        (((chosenPsi W).app (op zeroIndex)).app (op ⦋0⦌) x) =
      expectedVertexEquiv W x := by
  exact chosenPsiZeroFormula_of_gamma W
    (fun f => JTFrameGeneratorCalibration.frameGeneratorEquiv_eq_native
      (rigidCoefficient (chosenT W)) (zeroIndex, ⦋0⦌) f) x

/-- Literal bijectivity of the chosenPsi degree-zero component. -/
theorem chosenPsi_zero_bijective (W : Source) :
    Function.Bijective
      (((chosenPsi W).app (op zeroIndex)).app (op ⦋0⦌)) :=
  chosenPsi_zero_bijective_of_formula W (chosenPsi_vertex_expected W)

end

end DaggerModels.PartII.JTChosenPsiVertices
