import DaggerModelsPartII.JTCEReversalPushout
import DaggerModelsPartII.JTXiTwoCopyFrame
import DaggerModelsPartII.JTXiRawSeamPushout
import DaggerModelsPartII.PushoutCommonSeam
import DaggerModels.ForgetfulReflection

/-!
# The strict endpoint-collapse isomorphism for the actual Xi frame

The two actual interval copies and their common endpoint collapse give a
pushout of CE and CE.op over the same ordered boundary. The comparison is
exactly the already fixed adjoint extension actualFreeCEToRaw. Its inverse
therefore preserves the original boundary and parameter naturality.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTXiStrictEndpointIso

open JTXiEndpointCollapse JTXiEndpointCollapseBoundary
open JTCEReversalPushout JTXiTwoCopyFrame JTCEVertices
open GroupoidSimplex GroupoidSimplexReversal

noncomputable section

private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits

private def forwardQuotient (k : SimplexCategory) :
    CE.obj k ⟶ (rawCollapse.obj k).toSSet :=
  (CEToRaw boundaryCompatibility).app k

private def rawFrameLeg (k : SimplexCategory) :
    (frame1.obj k).toSSet ⟶ (rawCollapse.obj k).toSSet :=
  DaggerSSet.forget.map ((pushout.inl rawFaces rawEndpoints).app k)

private def reverseQuotient (k : SimplexCategory) :
    (CE.obj k).op ⟶ (rawCollapse.obj k).toSSet :=
  SSet.opFunctor.map (forwardQuotient k) ≫ (rawCollapse.obj k).daggerIso.inv

private theorem forwardQuotient_interval (k : SimplexCategory) :
    CE_interval.app k ≫ forwardQuotient k = forwardFrame.app k ≫ rawFrameLeg k := by
  exact NatTrans.congr_app
    (pushout.inl_desc forwardRaw boundaryToRaw boundaryCompatibility) k

private theorem forwardQuotient_boundary (k : SimplexCategory) :
    CE_boundary.app k ≫ forwardQuotient k = boundaryToRaw.app k := by
  exact NatTrans.congr_app
    (pushout.inr_desc forwardRaw boundaryToRaw boundaryCompatibility) k

private theorem boundary_dagger_fixed (Y : DaggerSSet.{0}) (f : boundary ⟶ Y.toSSet) :
    boundaryReversalIso.hom ≫ SSet.opFunctor.map f ≫ Y.daggerIso.inv = f := by
  have hb : boundaryVerticesIso.hom ≫ boundaryReversalIso.hom =
      SSetVertices.opInclusion boundary := by
    simp only [boundaryReversalIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact SSetVertices.opIso_hom_op_inclusion boundary
  apply (cancel_epi boundaryVerticesIso.hom).1
  calc
    _ = (boundaryVerticesIso.hom ≫ boundaryReversalIso.hom) ≫
          SSet.opFunctor.map f ≫ Y.daggerIso.inv := by rw [Category.assoc]
    _ = SSetVertices.opInclusion boundary ≫
          SSet.opFunctor.map f ≫ Y.daggerIso.inv := by rw [hb]
    _ = boundaryVerticesIso.hom ≫ f := (FreeDaggerPushout.desc_agreement f).symm

private theorem rawFrameLeg_inverse_dagger (k : SimplexCategory) :
    SSet.opFunctor.map (rawFrameLeg k) ≫ (rawCollapse.obj k).daggerIso.inv =
      (frame1.obj k).daggerIso.inv ≫ rawFrameLeg k := by
  let eS := DaggerSSet.daggerIso (frame1.obj k)
  let eT := DaggerSSet.daggerIso (rawCollapse.obj k)
  have h : rawFrameLeg k ≫ eT.hom = eS.hom ≫ SSet.opFunctor.map (rawFrameLeg k) :=
    ((pushout.inl rawFaces rawEndpoints).app k).comm
  change SSet.opFunctor.map (rawFrameLeg k) ≫ eT.inv = eS.inv ≫ rawFrameLeg k
  apply (cancel_mono eT.hom).1
  calc
    _ = SSet.opFunctor.map (rawFrameLeg k) := by simp only [Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    _ = (eS.inv ≫ eS.hom) ≫ SSet.opFunctor.map (rawFrameLeg k) := by
      simp only [Iso.inv_hom_id, Category.id_comp]
    _ = (eS.inv ≫ rawFrameLeg k) ≫ eT.hom := by
      simpa only [Category.assoc] using
        (congrArg (fun q ↦ eS.inv ≫ q) h).symm

private theorem reverseQuotient_interval (k : SimplexCategory) :
    reverseCEInterval k ≫ reverseQuotient k = reverseFrame k ≫ rawFrameLeg k := by
  change ((𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
      SSet.opFunctor.map (CE_interval.app k)) ≫
        (SSet.opFunctor.map (forwardQuotient k) ≫ (rawCollapse.obj k).daggerIso.inv) = _
  rw [Category.assoc, ← SSet.opFunctor.map_comp_assoc, forwardQuotient_interval,
    SSet.opFunctor.map_comp]
  simp only [Category.assoc]
  rw [rawFrameLeg_inverse_dagger]
  rw [reverseFrame_calibration]
  simp only [Category.assoc]

private theorem reverseQuotient_boundary (k : SimplexCategory) :
    reverseCEBoundary k ≫ reverseQuotient k = boundaryToRaw.app k := by
  change (boundaryReversalIso.hom ≫ SSet.opFunctor.map (CE_boundary.app k)) ≫
      (SSet.opFunctor.map (forwardQuotient k) ≫ (rawCollapse.obj k).daggerIso.inv) = _
  rw [Category.assoc, ← SSet.opFunctor.map_comp_assoc, forwardQuotient_boundary]
  exact boundary_dagger_fixed (rawCollapse.obj k) (boundaryToRaw.app k)

/-- The actual raw quotient has the two-copy CE pushout, with its original
forward quotient and the reverse determined by the actual dagger. -/
theorem rawCollapsedCopies_isPushout (k : SimplexCategory) :
    IsPushout (CE_boundary.app k) (reverseCEBoundary k)
      (forwardQuotient k) (reverseQuotient k) := by
  exact PushoutCommonSeam.isPushout
    (frame_isPushout k) (forward_isPushout k) (reverse_isPushout k)
    (JTXiRawSeamPushout.rawSeam_isPushout k)
    (forwardQuotient_interval k) (reverseQuotient_interval k)
    (forwardQuotient_boundary k) (reverseQuotient_boundary k)

private def concreteFreeToRaw (k : SimplexCategory) :
    FreeDaggerPushout.obj (CE.obj k) ⟶ rawCollapse.obj k :=
  (FreeDaggerPushout.isoFreeDagger.app (CE.obj k)).hom ≫ actualFreeCEToRaw.app k

private theorem concreteFreeToRaw_inl (k : SimplexCategory) :
    FreeDaggerPushout.inl (CE.obj k) ≫ (concreteFreeToRaw k).hom =
      forwardQuotient k := by
  change FreeDaggerPushout.inl (CE.obj k) ≫
      (DaggerSSet.forget.map (FreeDaggerPushout.isoFreeDagger.app (CE.obj k)).hom ≫
        DaggerSSet.forget.map (actualFreeCEToRaw.app k)) = _
  have hu := FreeDaggerPushout.inl_isoFreeDagger_hom (CE.obj k)
  change FreeDaggerPushout.inl (CE.obj k) ≫
      DaggerSSet.forget.map (FreeDaggerPushout.isoFreeDagger.app (CE.obj k)).hom =
        freeDaggerAdjunction.unit.app (CE.obj k) at hu
  rw [← Category.assoc, hu]
  rw [← freeDaggerAdjunction.homEquiv_unit]
  exact (freeDaggerAdjunction.homEquiv (CE.obj k) (rawCollapse.obj k)).apply_symm_apply
    (forwardQuotient k)

private theorem concreteFreeToRaw_inr (k : SimplexCategory) :
    FreeDaggerPushout.inr (CE.obj k) ≫ (concreteFreeToRaw k).hom =
      reverseQuotient k := by
  rw [FreeDaggerPushout.inr_hom, concreteFreeToRaw_inl]
  rfl

private theorem concreteFreeToRaw_hom_isIso (k : SimplexCategory) :
    IsIso (concreteFreeToRaw k).hom := by
  let e := (free_isPushout k).isoIsPushout _ _ (rawCollapsedCopies_isPushout k)
  have he : (concreteFreeToRaw k).hom = e.hom := by
    apply (free_isPushout k).hom_ext
    · rw [concreteFreeToRaw_inl]
      exact ((free_isPushout k).inl_isoIsPushout_hom _ _
        (rawCollapsedCopies_isPushout k)).symm
    · rw [concreteFreeToRaw_inr]
      exact ((free_isPushout k).inr_isoIsPushout_hom _ _
        (rawCollapsedCopies_isPushout k)).symm
  rw [he]
  infer_instance

/-- The original fixed free-CE-to-raw-Xi map is invertible in every degree. -/
theorem actualFreeCEToRaw_app_isIso (k : SimplexCategory) :
    IsIso (actualFreeCEToRaw.app k) := by
  letI : DaggerSSet.forget.{0}.ReflectsIsomorphisms :=
    DaggerSSet.forget_reflectsIsomorphisms
  haveI : IsIso (DaggerSSet.forget.map (concreteFreeToRaw k)) := by
    change IsIso (concreteFreeToRaw k).hom
    exact concreteFreeToRaw_hom_isIso k
  have hIso : IsIso (concreteFreeToRaw k) :=
    isIso_of_reflects_iso (concreteFreeToRaw k) DaggerSSet.forget
  change IsIso ((FreeDaggerPushout.isoFreeDagger.app (CE.obj k)).hom ≫
    actualFreeCEToRaw.app k) at hIso
  exact IsIso.of_isIso_comp_left
    ((FreeDaggerPushout.isoFreeDagger.app (CE.obj k)).hom) (actualFreeCEToRaw.app k)

/-- The same specified natural map is a natural isomorphism. -/
instance actualFreeCEToRaw_isIso : IsIso actualFreeCEToRaw := by
  letI (k : SimplexCategory) : IsIso (actualFreeCEToRaw.app k) :=
    actualFreeCEToRaw_app_isIso k
  exact NatIso.isIso_of_isIso_app actualFreeCEToRaw

/-- The manuscript's raw strict isomorphism, oriented from Xi collapse to CE. -/
def rawXiCollapseIso : rawCollapse ≅ CEFree :=
  (asIso actualFreeCEToRaw).symm

/-- The strict isomorphism preserves the same original ordered boundary. -/
theorem rawBoundary_rawXiCollapseIso :
    rawBoundary ≫ rawXiCollapseIso.hom = CEFreeBoundary := by
  rw [← actualBoundaryCalibration]
  simp only [rawXiCollapseIso, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

end

end DaggerModels.PartII.JTXiStrictEndpointIso
