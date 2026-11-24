import DaggerModelsPartII.JTXiFrameDaggerCalibration
import DaggerModelsPartII.JTXiEndpointCollapseBoundary
import DaggerModelsPartII.JTCEVertices

/-!
# The two-copy presentation of the degree-one JT frame

The actual frame at horizontal degree one is compared with the product
of the free dagger interval's explicit two-copy pushout and the groupoid
simplex parameter. Both copies retain the actual groupoid inversion.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTXiTwoCopyFrame

open JTXiEndpointCollapse JTXiEndpointCollapseBoundary
open DaggerJTFrameUnderlying JTXiFrameDaggerCalibration
open JTCEVertices GroupoidSimplex GroupoidSimplexReversal

noncomputable section

/-- The actual dagger isomorphism from the represented reversal interval
to the concrete two-copy free dagger interval. -/
def intervalDaggerIso :
    reversalSimplex.obj m1 ≅ FreeDaggerPushout.obj interval :=
  reversalSimplexFreeIso.app ⦋1⦌ ≪≫
    (FreeDaggerPushout.isoFreeDagger.app interval).symm

/-- The first copy of the represented interval becomes the literal first
coprojection of the concrete free dagger pushout. -/
theorem forwardSimplex_intervalDaggerIso :
    forwardSimplex ≫ intervalDaggerIso.hom.hom =
      FreeDaggerPushout.inl interval := by
  have hrev := congrArg DaggerSSet.Hom.hom
    (Iso.inv_hom_id (reversalSimplexFreeIso.app ⦋1⦌))
  have hfree := congrArg DaggerSSet.Hom.hom
    (Iso.hom_inv_id (FreeDaggerPushout.isoFreeDagger.app interval))
  change (reversalSimplexFreeIso.app ⦋1⦌).inv.hom ≫
      (reversalSimplexFreeIso.app ⦋1⦌).hom.hom = 𝟙 _ at hrev
  change (FreeDaggerPushout.isoFreeDagger.app interval).hom.hom ≫
      (FreeDaggerPushout.isoFreeDagger.app interval).inv.hom = 𝟙 _ at hfree
  change (FreeDaggerPushout.inl interval ≫
      (FreeDaggerPushout.isoFreeDagger.app interval).hom.hom ≫
      (reversalSimplexFreeIso.app ⦋1⦌).inv.hom) ≫
      ((reversalSimplexFreeIso.app ⦋1⦌).hom.hom ≫
        (FreeDaggerPushout.isoFreeDagger.app interval).inv.hom) = _
  calc
    _ = (FreeDaggerPushout.inl interval ≫
          (FreeDaggerPushout.isoFreeDagger.app interval).hom.hom) ≫
            ((reversalSimplexFreeIso.app ⦋1⦌).inv.hom ≫
              (reversalSimplexFreeIso.app ⦋1⦌).hom.hom) ≫
                (FreeDaggerPushout.isoFreeDagger.app interval).inv.hom := by
                  simp only [Category.assoc]
    _ = (FreeDaggerPushout.inl interval ≫
          (FreeDaggerPushout.isoFreeDagger.app interval).hom.hom) ≫
            (FreeDaggerPushout.isoFreeDagger.app interval).inv.hom := by
              rw [hrev]
              rfl
    _ = _ := by
          rw [Category.assoc, hfree]
          rfl

/-- The native represented degree-one frame as the two-copy free dagger
interval, multiplied by the actual groupoid parameter. -/
def frameOneUnderlyingIso (k : SimplexCategory) :
    (frame1.obj k).toSSet ≅
      FreeDaggerPushout.underlying interval ⊗ parameter.obj k :=
  (frameUnderlyingIso.app (m1, k)) ≪≫
    tensorIso
      (DaggerSSet.forget.mapIso intervalDaggerIso)
      (Iso.refl _)

/-- Tensor the actual two-copy free interval pushout by `J^k`. -/
private theorem intervalTwoCopyPushout (k : SimplexCategory) :
    IsPushout
      (SSetVertices.inclusion interval ▷ parameter.obj k)
      (SSetVertices.opInclusion interval ▷ parameter.obj k)
      (FreeDaggerPushout.inl interval ▷ parameter.obj k)
      (FreeDaggerPushout.inr interval ▷ parameter.obj k) := by
  exact (IsPushout.of_hasPushout
    (SSetVertices.inclusion interval)
    (SSetVertices.opInclusion interval)).map
      (MonoidalCategory.tensorRight (parameter.obj k))

/-- The reverse copy inside the actual degree-one represented frame. -/
def reverseFrame (k : SimplexCategory) :
    interval.op ⊗ parameter.obj k ⟶ (frame1.obj k).toSSet :=
  (FreeDaggerPushout.inr interval ▷ parameter.obj k) ≫
    (frameOneUnderlyingIso k).inv

/-- The literal forward-copy calibration required for transporting the
two-copy pushout. It is kept as an explicit proof target until the
adjunction-unit and natural-isomorphism cancellations are checked. -/
def ForwardFrameCalibration (k : SimplexCategory) : Prop :=
  forwardFrame.app k ≫ (frameOneUnderlyingIso k).hom =
    FreeDaggerPushout.inl interval ▷ parameter.obj k

theorem forwardFrame_calibration (k : SimplexCategory) :
    ForwardFrameCalibration k := by
  have hfirst :
      forwardFrame.app k ≫ (frameUnderlyingIso.app (m1, k)).hom =
        forwardSimplex ⊗ₘ 𝟙 (parameter.obj k) := by
    change ((forwardSimplex ⊗ₘ 𝟙 (parameter.obj k)) ≫
      (frameUnderlyingIso.app (m1, k)).inv) ≫
        (frameUnderlyingIso.app (m1, k)).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (forwardFrame.app k ≫ (frameUnderlyingIso.app (m1, k)).hom) ≫
      (intervalDaggerIso.hom.hom ⊗ₘ 𝟙 (parameter.obj k)) = _
  rw [hfirst, tensorHom_comp_tensorHom, Category.id_comp,
    forwardSimplex_intervalDaggerIso]
  rfl

/-- The precise degree-one dagger square. The second factor is the
actual inversion of the groupoid parameter. -/
def FrameOneDaggerCalibration (k : SimplexCategory) : Prop :=
  (frameOneUnderlyingIso k).hom ≫
      ((FreeDaggerPushout.obj interval).dagger ⊗ₘ
        (daggerParameter.obj k).dagger) =
    (frame1.obj k).dagger ≫
      SSet.opFunctor.map (frameOneUnderlyingIso k).hom

theorem frameOne_dagger (k : SimplexCategory) :
    FrameOneDaggerCalibration k := by
  let e := intervalDaggerIso
  let a := (frameUnderlyingIso.app (m1, k)).hom
  let b := e.hom.hom ⊗ₘ 𝟙 (parameter.obj k)
  let d := (reversalSimplex.obj m1).dagger ⊗ₘ (daggerParameter.obj k).dagger
  let d' := (FreeDaggerPushout.obj interval).dagger ⊗ₘ
    (daggerParameter.obj k).dagger
  have he : e.hom.hom ≫ (FreeDaggerPushout.obj interval).dagger =
      (reversalSimplex.obj m1).dagger ≫
        SSet.opFunctor.map e.hom.hom := e.hom.comm
  have hb : b ≫ d' = d ≫ SSet.opFunctor.map b := by
    change (e.hom.hom ⊗ₘ 𝟙 (parameter.obj k)) ≫
        ((FreeDaggerPushout.obj interval).dagger ⊗ₘ
          (daggerParameter.obj k).dagger) =
      ((reversalSimplex.obj m1).dagger ⊗ₘ
        (daggerParameter.obj k).dagger) ≫
          (SSet.opFunctor.map e.hom.hom ⊗ₘ 𝟙 _)
    simp only [tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
    exact congrArg₂ (fun f g ↦ f ⊗ₘ g) he rfl
  have ha : a ≫ d = (frame1.obj k).dagger ≫
      SSet.opFunctor.map a := frameUnderlyingIso_dagger (m1, k)
  change (a ≫ b) ≫ d' =
    (frame1.obj k).dagger ≫ SSet.opFunctor.map (a ≫ b)
  calc
    _ = a ≫ (b ≫ d') := Category.assoc _ _ _
    _ = a ≫ (d ≫ SSet.opFunctor.map b) := by rw [hb]
    _ = (a ≫ d) ≫ SSet.opFunctor.map b := by rw [Category.assoc]
    _ = ((frame1.obj k).dagger ≫ SSet.opFunctor.map a) ≫
          SSet.opFunctor.map b := by rw [ha]
    _ = _ := by rw [Category.assoc, Functor.map_comp]

/-- The desired reverse-copy normalization, with actual inversion of
`J^k` and the native opposite-tensor identification. -/
def ReverseFrameCalibration (k : SimplexCategory) : Prop :=
  reverseFrame k =
    (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
      SSet.opFunctor.map (forwardFrame.app k) ≫
        (DaggerSSet.daggerIso (frame1.obj k)).inv

set_option maxRecDepth 100000 in
theorem reverseFrame_calibration (k : SimplexCategory) :
    ReverseFrameCalibration k := by
  let F := frameOneUnderlyingIso k
  let P := tensorIso
    (DaggerSSet.daggerIso (FreeDaggerPushout.obj interval))
    (DaggerSSet.daggerIso (daggerParameter.obj k))
  have hs : F.hom ≫ P.hom =
      (frame1.obj k).dagger ≫ SSet.opFunctor.map F.hom :=
    frameOne_dagger k
  have hDi : (DaggerSSet.daggerIso (frame1.obj k)).inv ≫ F.hom =
      SSet.opFunctor.map F.hom ≫ P.inv := by
    apply (cancel_mono P.hom).1
    calc
      _ = (DaggerSSet.daggerIso (frame1.obj k)).inv ≫
            (F.hom ≫ P.hom) := Category.assoc _ _ _
      _ = (DaggerSSet.daggerIso (frame1.obj k)).inv ≫
            ((frame1.obj k).dagger ≫ SSet.opFunctor.map F.hom) := by
              rw [hs]
      _ = SSet.opFunctor.map F.hom := by
            have hcancel :=
              (DaggerSSet.daggerIso (frame1.obj k)).inv_hom_id
            change ((DaggerSSet.daggerIso (frame1.obj k)).inv ≫
              (DaggerSSet.daggerIso (frame1.obj k)).hom) ≫
                SSet.opFunctor.map F.hom = _
            rw [hcancel]
            simp only [Category.id_comp]
      _ = (SSet.opFunctor.map F.hom ≫ P.inv) ≫ P.hom := by
            simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcopy :
      (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
        SSet.opFunctor.map
          (FreeDaggerPushout.inl interval ▷ parameter.obj k) ≫ P.inv =
      FreeDaggerPushout.inr interval ▷ parameter.obj k := by
    change (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
      (SSet.opFunctor.map (FreeDaggerPushout.inl interval) ⊗ₘ
        𝟙 (parameter.obj k).op) ≫
      ((DaggerSSet.daggerIso (FreeDaggerPushout.obj interval)).inv ⊗ₘ
        (DaggerSSet.daggerIso (daggerParameter.obj k)).inv) = _
    simp only [tensorHom_comp_tensorHom, Category.id_comp]
    have hi : SSet.opFunctor.map (FreeDaggerPushout.inl interval) ≫
        (DaggerSSet.daggerIso (FreeDaggerPushout.obj interval)).inv =
          FreeDaggerPushout.inr interval := by
      apply (cancel_mono
        (DaggerSSet.daggerIso (FreeDaggerPushout.obj interval)).hom).1
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change SSet.opFunctor.map (FreeDaggerPushout.inl interval) =
        FreeDaggerPushout.inr interval ≫ FreeDaggerPushout.daggerMap interval
      exact (FreeDaggerPushout.inr_daggerMap interval).symm
    rw [hi]
    change FreeDaggerPushout.inr interval ⊗ₘ
      ((DaggerSSet.daggerIso (daggerParameter.obj k)).hom ≫
        (DaggerSSet.daggerIso (daggerParameter.obj k)).inv) =
          FreeDaggerPushout.inr interval ⊗ₘ 𝟙 _
    rw [Iso.hom_inv_id]
  apply (cancel_mono F.hom).1
  calc
    reverseFrame k ≫ F.hom =
        FreeDaggerPushout.inr interval ▷ parameter.obj k := by
          change ((FreeDaggerPushout.inr interval ▷ parameter.obj k) ≫
            F.inv) ≫ F.hom = _
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
          SSet.opFunctor.map
            (FreeDaggerPushout.inl interval ▷ parameter.obj k) ≫ P.inv :=
      hcopy.symm
    _ = (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
          SSet.opFunctor.map (forwardFrame.app k ≫ F.hom) ≫ P.inv := by
            rw [forwardFrame_calibration]
    _ = ((𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
          SSet.opFunctor.map (forwardFrame.app k)) ≫
            (SSet.opFunctor.map F.hom ≫ P.inv) := by
          rw [Functor.map_comp]
          simp only [Category.assoc]
    _ = ((𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
          SSet.opFunctor.map (forwardFrame.app k)) ≫
            ((DaggerSSet.daggerIso (frame1.obj k)).inv ≫ F.hom) := by
          rw [hDi]
    _ = _ := by simp only [Category.assoc]

/-- The actual degree-one JT frame is the pushout of its two interval
copies over the boundary-vertex seam. The seam is parametrized by the
literal `boundary` used in `cylinderInclusion` and in the raw collapse. -/
theorem frame_isPushout (k : SimplexCategory) :
    IsPushout (cylinderInclusion.app k)
      ((JTCEVertices.boundaryAsVertices.hom ≫
          SSetVertices.opInclusion interval) ▷ parameter.obj k)
      (forwardFrame.app k) (reverseFrame k) := by
  let e : SSetVertices.obj interval ⊗ parameter.obj k ≅
      boundaryCylinder.obj k :=
    tensorIso JTCEVertices.boundaryAsVertices.symm (Iso.refl _)
  apply (intervalTwoCopyPushout k).of_iso e
    (Iso.refl _) (Iso.refl _) (frameOneUnderlyingIso k).symm
  · change (SSetVertices.inclusion interval ⊗ₘ 𝟙 (parameter.obj k)) ≫ 𝟙 _ =
        (JTCEVertices.boundaryAsVertices.symm.hom ⊗ₘ 𝟙 _) ≫
          ((SSet.boundary 1).ι ⊗ₘ 𝟙 _)
    simp only [Category.comp_id, tensorHom_comp_tensorHom]
    congr 1
    calc
      SSetVertices.inclusion interval =
          JTCEVertices.boundaryAsVertices.symm.hom ≫
            (JTCEVertices.boundaryAsVertices.hom ≫
              SSetVertices.inclusion interval) := by
            simp only [Iso.symm_hom, ← Category.assoc,
              Iso.inv_hom_id, Category.id_comp]
      _ = JTCEVertices.boundaryAsVertices.symm.hom ≫
            (SSet.boundary 1).ι := by
            rw [JTCEVertices.boundaryAsVertices_inclusion]
  · change (SSetVertices.opInclusion interval ⊗ₘ 𝟙 (parameter.obj k)) ≫ 𝟙 _ =
        (JTCEVertices.boundaryAsVertices.symm.hom ⊗ₘ 𝟙 _) ≫
          ((JTCEVertices.boundaryAsVertices.hom ≫
            SSetVertices.opInclusion interval) ⊗ₘ 𝟙 _)
    simp only [Category.comp_id, tensorHom_comp_tensorHom,
      Iso.symm_hom, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  · change (FreeDaggerPushout.inl interval ▷ parameter.obj k) ≫
        (frameOneUnderlyingIso k).inv = 𝟙 _ ≫ forwardFrame.app k
    rw [Category.id_comp]
    apply (cancel_mono (frameOneUnderlyingIso k).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (forwardFrame_calibration k).symm
  · change (FreeDaggerPushout.inr interval ▷ parameter.obj k) ≫
        (frameOneUnderlyingIso k).inv = 𝟙 _ ≫ reverseFrame k
    rw [Category.id_comp]
    rfl

end

end DaggerModels.PartII.JTXiTwoCopyFrame
