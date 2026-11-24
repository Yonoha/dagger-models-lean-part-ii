import DaggerModelsPartII.JTRightAdjointOrderedFiber
import DaggerModelsPartII.JTXiTwoCopyFrame
import DaggerModelsPartII.JTWalkingUnitaryWeak
import DaggerModels.FreeDaggerPushout

/-!
# The original right-adjoint endpoint square

The actual two-copy represented frame determines a unique dagger map from
an ordinary forward map and two compatible dagger endpoint maps. This
degreewise inverse proves that the original underlying right-adjoint
comparison square over the ordered endpoint pair is a pullback of
simplicial sets, in every simplex degree and for every dagger simplicial set.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTRightEndpointCartesian

open JTXiEndpointCollapse JTXiTwoCopyFrame
open JTXiEndpointCollapseBoundary JTXiFrameDaggerCalibration
open DaggerJTFrameUnderlying
open DaggerJTAdjunction JTRightAdjointNativeRow JTOrderedFrameMate
open JTUnderlyingOrderedFibers OrdinaryJTRealization

noncomputable section

private local instance : SSet.opFunctor.IsEquivalence :=
  show SSet.opEquivalence.functor.IsEquivalence by infer_instance

private def zeroFrameUnderlyingIsTerminal :
    IsTerminal (underlyingSimplex.obj m0) := by
  letI : PreservesLimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesLimits
  have h : IsTerminal ((freeDagger.obj (Δ[0] : SSet.{0})).toSSet) :=
    JTWalkingUnitaryWeak.freeZeroIsTerminal.isTerminalObj
      DaggerSSet.forget _
  exact IsTerminal.ofIso h
    (DaggerSSet.forget.mapIso (reversalSimplexFreeIso.app ⦋0⦌)).symm

private theorem forwardSimplex_zero_isIso :
    IsIso (forwardSimplexNat.app ⦋0⦌) :=
  isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀
    zeroFrameUnderlyingIsTerminal _

private theorem forwardFrame0_isIso (k : SimplexCategory) :
    IsIso (forwardFrame0.app k) := by
  letI : IsIso (forwardSimplexNat.app ⦋0⦌) :=
    forwardSimplex_zero_isIso
  haveI : IsIso (forwardParameter0.app k) := by
    change IsIso
      ((forwardSimplexNat.app ⦋0⦌) ⊗ₘ (𝟙 (GroupoidSimplex.parameter.obj k)))
    infer_instance
  dsimp only [forwardFrame0, NatTrans.comp_app]
  infer_instance

/-- The dagger on the point cylinder transported by the actual
degree-zero forward-copy isomorphism. The product-dagger theorem below
retains the specified inversion of `J[k]` after the represented frame iso. -/
def zeroCylinderDagger (k : SimplexCategory) :
    zeroCylinder.obj k ⟶ (zeroCylinder.obj k).op := by
  letI : IsIso (forwardFrame0.app k) := forwardFrame0_isIso k
  exact forwardFrame0.app k ≫ (frame0.obj k).dagger ≫
    SSet.opFunctor.map (inv (forwardFrame0.app k))

/-- The chosen zero-cylinder involution is exactly the transported
dagger of the original outer-zero represented frame. -/
theorem zeroCylinderDagger_forwardFrame0 (k : SimplexCategory) :
    zeroCylinderDagger k ≫ SSet.opFunctor.map (forwardFrame0.app k) =
      forwardFrame0.app k ≫ (frame0.obj k).dagger := by
  letI : IsIso (forwardFrame0.app k) := forwardFrame0_isIso k
  change (forwardFrame0.app k ≫ (frame0.obj k).dagger ≫
    SSet.opFunctor.map (inv (forwardFrame0.app k))) ≫
      SSet.opFunctor.map (forwardFrame0.app k) = _
  simp only [Category.assoc]
  rw [← SSet.opFunctor.map_comp, IsIso.inv_hom_id]
  rw [SSet.opFunctor.map_id, Category.comp_id]

/-- The actual degree-zero forward copy transports the frame dagger to the
specified product dagger. The horizontal point normalization is retained
explicitly; no trivial action on the parameter is assumed. -/
theorem forwardFrame0_productDagger (k : SimplexCategory) :
    (forwardFrame0.app k ≫ (frame0.obj k).dagger) ≫
      SSet.opFunctor.map (DaggerJTFrameUnderlying.frameUnderlyingIso.app (m0, k)).hom =
    forwardParameter0.app k ≫ (productDaggerIso (m0, k)).hom := by
  let e := DaggerJTFrameUnderlying.frameUnderlyingIso.app (m0, k)
  have hc : forwardFrame0.app k ≫ e.hom = forwardParameter0.app k := by
    change (forwardParameter0.app k ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hd := frameUnderlyingIso_dagger (m0, k)
  change e.hom ≫ (productDaggerIso (m0, k)).hom =
    (frame0.obj k).dagger ≫ SSet.opFunctor.map e.hom at hd
  calc
    (forwardFrame0.app k ≫ (frame0.obj k).dagger) ≫
        SSet.opFunctor.map e.hom =
      forwardFrame0.app k ≫
        ((frame0.obj k).dagger ≫ SSet.opFunctor.map e.hom) :=
          Category.assoc _ _ _
    _ = forwardFrame0.app k ≫
          (e.hom ≫ (productDaggerIso (m0, k)).hom) := by rw [hd]
    _ = forwardParameter0.app k ≫ (productDaggerIso (m0, k)).hom := by
          rw [← Category.assoc, hc]

/-- The selected ordered boundary cylinder leg. -/
private def boundaryLeg (i : Fin 2) (k : SimplexCategory) :
    zeroCylinder.obj k ⟶ boundaryCylinder.obj k :=
  ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
    GroupoidSimplex.parameter.obj k)

/-- The reverse-copy seam in the checked two-copy pushout. -/
private def reverseSeam (k : SimplexCategory) :
    boundaryCylinder.obj k ⟶
      interval.op ⊗ GroupoidSimplex.parameter.obj k :=
  ((JTCEVertices.boundaryAsVertices.hom ≫
      SSetVertices.opInclusion interval) ▷ GroupoidSimplex.parameter.obj k)

/-- The actual groupoid inversion gives the isomorphism from the reverse
interval cylinder to the reversal of the forward cylinder. -/
private def reverseTensorIso (k : SimplexCategory) :
    interval.op ⊗ GroupoidSimplex.parameter.obj k ≅
      (intervalCylinder.obj k).op :=
  tensorIso (Iso.refl interval.op)
    (DaggerSSet.daggerIso (GroupoidSimplexReversal.daggerParameter.obj k))

private theorem forwardFrame_mono (k : SimplexCategory) :
    Mono (forwardFrame.app k) := by
  haveI : Mono (FreeDaggerPushout.inl interval) := by
    rw [NatTrans.mono_iff_mono_app]
    intro q
    exact (mono_iff_injective _).2
      (FreeDaggerPushout.inl_app_injective interval q)
  haveI : Mono (FreeDaggerPushout.inl interval ▷
      GroupoidSimplex.parameter.obj k) :=
    DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono
      (FreeDaggerPushout.inl interval) (GroupoidSimplex.parameter.obj k)
  let F := frameOneUnderlyingIso k
  have h : Mono (forwardFrame.app k ≫ F.hom) := by
    rw [forwardFrame_calibration]
    infer_instance
  letI : Mono (forwardFrame.app k ≫ F.hom) := h
  have h' : Mono ((forwardFrame.app k ≫ F.hom) ≫ F.inv) := inferInstance
  have hc : (forwardFrame.app k ≫ F.hom) ≫ F.inv =
      forwardFrame.app k := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hc] at h'
  exact h'

/-- The reverse seam is the reversed forward seam for each ordered vertex,
where the zero-cylinder dagger is transported from the actual outer-zero
dagger frame. This includes inversion of the full `J[k]` parameter. -/
private theorem reverseSeam_vertex_dagger (i : Fin 2) (k : SimplexCategory) :
    (boundaryLeg i k ≫ reverseSeam k) ≫
        (𝟙 interval.op ⊗ₘ
          (GroupoidSimplexReversal.daggerParameter.obj k).dagger) =
      zeroCylinderDagger k ≫
        SSet.opFunctor.map (boundaryLeg i k ≫ cylinderInclusion.app k) := by
  let f := forwardFrame.app k
  let e := (frame1.obj k).daggerIso
  let d := (𝟙 interval.op ⊗ₘ
    (GroupoidSimplexReversal.daggerParameter.obj k).dagger)
  have hf : Mono f := forwardFrame_mono k
  letI : Mono f := hf
  letI : Mono (SSet.opFunctor.map f) := inferInstance
  have hw := (frame_isPushout k).w
  change cylinderInclusion.app k ≫ f = reverseSeam k ≫ reverseFrame k at hw
  have hv := frameEndpointSquare i k
  change boundaryLeg i k ≫ cylinderInclusion.app k ≫ f =
    forwardFrame0.app k ≫ ((frameEndpoint i).app k).hom at hv
  have hr := reverseFrame_calibration k
  change reverseFrame k = d ≫ SSet.opFunctor.map f ≫ e.inv at hr
  have hd := ((frameEndpoint i).app k).comm
  change ((frameEndpoint i).app k).hom ≫ e.hom =
    (frame0.obj k).dagger ≫
      SSet.opFunctor.map ((frameEndpoint i).app k).hom at hd
  apply (cancel_mono (SSet.opFunctor.map f)).1
  calc
    ((boundaryLeg i k ≫ reverseSeam k) ≫ d) ≫
        SSet.opFunctor.map f =
      (boundaryLeg i k ≫ reverseSeam k ≫ reverseFrame k) ≫ e.hom := by
        rw [hr]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (forwardFrame0.app k ≫ ((frameEndpoint i).app k).hom) ≫
          e.hom := by rw [← hw, hv]
    _ = (forwardFrame0.app k ≫ (frame0.obj k).dagger) ≫
          SSet.opFunctor.map ((frameEndpoint i).app k).hom := by
          rw [Category.assoc, hd]
          simp only [Category.assoc]
    _ = (zeroCylinderDagger k ≫
          SSet.opFunctor.map (forwardFrame0.app k)) ≫
            SSet.opFunctor.map ((frameEndpoint i).app k).hom := by
          rw [zeroCylinderDagger_forwardFrame0]
    _ = (zeroCylinderDagger k ≫
          SSet.opFunctor.map (boundaryLeg i k ≫
            cylinderInclusion.app k)) ≫ SSet.opFunctor.map f := by
          simp only [Category.assoc, ← SSet.opFunctor.map_comp]
          rw [hv]

/-- Involutivity turns the checked reverse-copy formula into the matching
forward-copy formula, with the actual parameter inversion. -/
private theorem forwardFrame_dagger (k : SimplexCategory) :
    forwardFrame.app k ≫ (frame1.obj k).dagger =
      SSet.opFunctorCompOpFunctorIso.inv.app (intervalCylinder.obj k) ≫
        SSet.opFunctor.map (reverseTensorIso k).inv ≫
          SSet.opFunctor.map (reverseFrame k) := by
  let A := (frame1.obj k).toSSet
  let F := intervalCylinder.obj k
  let d := reverseTensorIso k
  let e := DaggerSSet.daggerIso (frame1.obj k)
  have hr := reverseFrame_calibration k
  change reverseFrame k =
    d.hom ≫ SSet.opFunctor.map (forwardFrame.app k) ≫ e.inv at hr
  have hε := SSet.opFunctorCompOpFunctorIso.inv.naturality (forwardFrame.app k)
  change forwardFrame.app k ≫
      SSet.opFunctorCompOpFunctorIso.inv.app A =
    SSet.opFunctorCompOpFunctorIso.inv.app F ≫
      SSet.opFunctor.map (SSet.opFunctor.map (forwardFrame.app k)) at hε
  have hd := DaggerSSet.daggerIso_inv_op (frame1.obj k)
  change SSet.opFunctorCompOpFunctorIso.inv.app A ≫
      SSet.opFunctor.map e.inv = e.hom at hd
  change forwardFrame.app k ≫ e.hom =
    SSet.opFunctorCompOpFunctorIso.inv.app F ≫
      SSet.opFunctor.map d.inv ≫ SSet.opFunctor.map (reverseFrame k)
  calc
    forwardFrame.app k ≫ e.hom =
      forwardFrame.app k ≫
        (SSet.opFunctorCompOpFunctorIso.inv.app A ≫
          SSet.opFunctor.map e.inv) := by rw [hd]
    _ = (SSet.opFunctorCompOpFunctorIso.inv.app F ≫
          SSet.opFunctor.map (SSet.opFunctor.map (forwardFrame.app k))) ≫
            SSet.opFunctor.map e.inv := by rw [← Category.assoc, hε]
    _ = SSet.opFunctorCompOpFunctorIso.inv.app F ≫
          SSet.opFunctor.map d.inv ≫
            SSet.opFunctor.map
              (d.hom ≫ SSet.opFunctor.map (forwardFrame.app k) ≫ e.inv) := by
          simp only [← SSet.opFunctor.map_comp,
            ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
          simp only [Category.assoc, SSet.opFunctor.map_comp]
    _ = _ := by rw [← hr]

/-- The reverse interval copy is forced by a map on the forward copy and the
actual involutions of the parameter and target. -/
def forcedReverse (X : DaggerSSet.{0}) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet) :
    interval.op ⊗ GroupoidSimplex.parameter.obj k ⟶ X.toSSet :=
  (𝟙 interval.op ⊗ₘ (GroupoidSimplexReversal.daggerParameter.obj k).dagger) ≫
    SSet.opFunctor.map f ≫ X.daggerIso.inv

/-- The supplied dagger endpoint map turns compatibility on the forward
copy into agreement with the forced reverse copy on that seam vertex. -/
private theorem reverseSeam_agreement_vertex (X : DaggerSSet.{0})
    (i : Fin 2) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a : frame0.obj k ⟶ X)
    (ha : (boundaryLeg i k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a.hom) :
    (boundaryLeg i k ≫ reverseSeam k) ≫ forcedReverse X k f =
      (boundaryLeg i k ≫ cylinderInclusion.app k) ≫ f := by
  let eX := DaggerSSet.daggerIso X
  have hdagger : (frame0.obj k).dagger ≫
      SSet.opFunctor.map a.hom ≫ eX.inv = a.hom := by
    apply (cancel_mono eX.hom).1
    calc
      ((frame0.obj k).dagger ≫ SSet.opFunctor.map a.hom ≫ eX.inv) ≫
          eX.hom =
        (frame0.obj k).dagger ≫ SSet.opFunctor.map a.hom := by
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = a.hom ≫ eX.hom := a.comm.symm
  calc
    (boundaryLeg i k ≫ reverseSeam k) ≫ forcedReverse X k f =
      ((boundaryLeg i k ≫ reverseSeam k) ≫
        (𝟙 interval.op ⊗ₘ
          (GroupoidSimplexReversal.daggerParameter.obj k).dagger)) ≫
          SSet.opFunctor.map f ≫ eX.inv := by
            rfl
    _ = (zeroCylinderDagger k ≫
          SSet.opFunctor.map (boundaryLeg i k ≫
            cylinderInclusion.app k)) ≫
              SSet.opFunctor.map f ≫ eX.inv := by
            rw [reverseSeam_vertex_dagger]
    _ = zeroCylinderDagger k ≫
          SSet.opFunctor.map
            ((boundaryLeg i k ≫ cylinderInclusion.app k) ≫ f) ≫
              eX.inv := by
            simp only [Category.assoc, SSet.opFunctor.map_comp]
    _ = zeroCylinderDagger k ≫
          SSet.opFunctor.map (forwardFrame0.app k ≫ a.hom) ≫
            eX.inv := by rw [ha]
    _ = (zeroCylinderDagger k ≫
          SSet.opFunctor.map (forwardFrame0.app k)) ≫
            SSet.opFunctor.map a.hom ≫ eX.inv := by
            simp only [SSet.opFunctor.map_comp, Category.assoc]
    _ = (forwardFrame0.app k ≫ (frame0.obj k).dagger) ≫
          SSet.opFunctor.map a.hom ≫ eX.inv := by
            rw [zeroCylinderDagger_forwardFrame0]
    _ = forwardFrame0.app k ≫ a.hom := by
          simp only [Category.assoc, hdagger]
    _ = (boundaryLeg i k ≫ cylinderInclusion.app k) ≫ f := ha.symm

/-- Two compatible dagger endpoint rows force agreement of the ordinary
forward map and its involutive reverse on the entire actual seam. -/
theorem seam_agreement (X : DaggerSSet.{0}) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom) :
    cylinderInclusion.app k ≫ f =
      reverseSeam k ≫ forcedReverse X k f := by
  apply SSet.boundary₁.hom_ext_rightTensor
  · exact (reverseSeam_agreement_vertex X 0 k f a₀ h₀).symm
  · exact (reverseSeam_agreement_vertex X 1 k f a₁ h₁).symm

/-- The underlying simplicial map extending compatible forward and endpoint
data across the actual two-copy outer-one frame. Its dagger compatibility is
a separate equation below. -/
def underlyingExtension (X : DaggerSSet.{0}) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom) :
    (frame1.obj k).toSSet ⟶ X.toSSet :=
  (frame_isPushout k).desc f (forcedReverse X k f)
    (seam_agreement X k f a₀ a₁ h₀ h₁)

theorem forward_underlyingExtension (X : DaggerSSet.{0}) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom) :
    forwardFrame.app k ≫ underlyingExtension X k f a₀ a₁ h₀ h₁ = f :=
  (frame_isPushout k).inl_desc _ _ _

theorem reverse_underlyingExtension (X : DaggerSSet.{0}) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom) :
    reverseFrame k ≫ underlyingExtension X k f a₀ a₁ h₀ h₁ =
      forcedReverse X k f :=
  (frame_isPushout k).inr_desc _ _ _

private theorem forcedReverse_dagger (X : DaggerSSet.{0})
    (k : SimplexCategory) (f : intervalCylinder.obj k ⟶ X.toSSet) :
    forcedReverse X k f ≫ X.dagger =
      (reverseTensorIso k).hom ≫ SSet.opFunctor.map f := by
  change (((reverseTensorIso k).hom ≫
      SSet.opFunctor.map f) ≫ X.daggerIso.inv) ≫ X.daggerIso.hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The pushout extension of a compatible forward map and dagger endpoint
rows is itself a genuine dagger simplicial map. -/
private theorem underlyingExtension_comm (X : DaggerSSet.{0})
    (k : SimplexCategory) (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom) :
    underlyingExtension X k f a₀ a₁ h₀ h₁ ≫ X.dagger =
      (frame1.obj k).dagger ≫
        SSet.opFunctor.map (underlyingExtension X k f a₀ a₁ h₀ h₁) := by
  let g := underlyingExtension X k f a₀ a₁ h₀ h₁
  let d := reverseTensorIso k
  let eX := DaggerSSet.daggerIso X
  have hf : forwardFrame.app k ≫ g = f :=
    forward_underlyingExtension X k f a₀ a₁ h₀ h₁
  have hr : reverseFrame k ≫ g = forcedReverse X k f :=
    reverse_underlyingExtension X k f a₀ a₁ h₀ h₁
  have hε := SSet.opFunctorCompOpFunctorIso.inv.naturality f
  change f ≫ SSet.opFunctorCompOpFunctorIso.inv.app X.toSSet =
    SSet.opFunctorCompOpFunctorIso.inv.app (intervalCylinder.obj k) ≫
      SSet.opFunctor.map (SSet.opFunctor.map f) at hε
  have hd := DaggerSSet.daggerIso_inv_op X
  change SSet.opFunctorCompOpFunctorIso.inv.app X.toSSet ≫
    SSet.opFunctor.map eX.inv = eX.hom at hd
  apply (frame_isPushout k).hom_ext
  · calc
      forwardFrame.app k ≫ (g ≫ X.dagger) = f ≫ X.dagger := by
        rw [← Category.assoc, hf]
      _ = f ≫ (SSet.opFunctorCompOpFunctorIso.inv.app X.toSSet ≫
            SSet.opFunctor.map eX.inv) := by
              change f ≫ eX.hom = _
              rw [hd]
      _ = (SSet.opFunctorCompOpFunctorIso.inv.app
              (intervalCylinder.obj k) ≫
            SSet.opFunctor.map (SSet.opFunctor.map f)) ≫
              SSet.opFunctor.map eX.inv := by rw [← Category.assoc, hε]
      _ = SSet.opFunctorCompOpFunctorIso.inv.app
              (intervalCylinder.obj k) ≫
            SSet.opFunctor.map d.inv ≫
              SSet.opFunctor.map
                (d.hom ≫ SSet.opFunctor.map f ≫ eX.inv) := by
            simp only [← SSet.opFunctor.map_comp,
              ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
            simp only [Category.assoc, SSet.opFunctor.map_comp]
      _ = SSet.opFunctorCompOpFunctorIso.inv.app
              (intervalCylinder.obj k) ≫
            SSet.opFunctor.map d.inv ≫
              SSet.opFunctor.map (reverseFrame k ≫ g) := by
            rw [hr]
            rfl
      _ = (forwardFrame.app k ≫ (frame1.obj k).dagger) ≫
              SSet.opFunctor.map g := by
            rw [forwardFrame_dagger]
            dsimp only [d]
            simp only [SSet.opFunctor.map_comp, Category.assoc]
      _ = forwardFrame.app k ≫
            ((frame1.obj k).dagger ≫ SSet.opFunctor.map g) :=
              Category.assoc _ _ _
  · calc
      reverseFrame k ≫ (g ≫ X.dagger) =
          forcedReverse X k f ≫ X.dagger := by
            rw [← Category.assoc, hr]
      _ = d.hom ≫ SSet.opFunctor.map f := forcedReverse_dagger X k f
      _ = (reverseFrame k ≫ (frame1.obj k).dagger) ≫
            SSet.opFunctor.map g := by
            have hi : (frame1.obj k).daggerIso.inv ≫
                (frame1.obj k).dagger = 𝟙 _ :=
              (frame1.obj k).daggerIso.inv_hom_id
            rw [reverseFrame_calibration]
            simp only [Category.assoc, hi]
            change d.hom ≫ SSet.opFunctor.map f =
              d.hom ≫ SSet.opFunctor.map (forwardFrame.app k) ≫
                SSet.opFunctor.map g
            rw [← SSet.opFunctor.map_comp, hf]
      _ = reverseFrame k ≫
            ((frame1.obj k).dagger ≫ SSet.opFunctor.map g) :=
              Category.assoc _ _ _

/-- The unique dagger extension of compatible ordinary forward and actual
dagger endpoint data across the checked two-copy frame. -/
def daggerExtension (X : DaggerSSet.{0}) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom) : frame1.obj k ⟶ X where
  hom := underlyingExtension X k f a₀ a₁ h₀ h₁
  comm := underlyingExtension_comm X k f a₀ a₁ h₀ h₁

/-- The actual forward copy of the extension is the supplied map. -/
theorem daggerExtension_forward (X : DaggerSSet.{0})
    (k : SimplexCategory) (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom) :
    forwardFrame.app k ≫ (daggerExtension X k f a₀ a₁ h₀ h₁).hom = f :=
  forward_underlyingExtension X k f a₀ a₁ h₀ h₁

/-- Either actual ordered endpoint of the extension recovers the specified
dagger endpoint map. -/
theorem daggerExtension_endpoint (X : DaggerSSet.{0})
    (i : Fin 2) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom)
    (a : frame0.obj k ⟶ X)
    (hi : (boundaryLeg i k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a.hom) :
    (frameEndpoint i).app k ≫ daggerExtension X k f a₀ a₁ h₀ h₁ = a := by
  apply DaggerSSet.Hom.ext
  letI : IsIso (forwardFrame0.app k) := forwardFrame0_isIso k
  apply (cancel_epi (forwardFrame0.app k)).1
  have hv := frameEndpointSquare i k
  change boundaryLeg i k ≫ cylinderInclusion.app k ≫
    forwardFrame.app k =
      forwardFrame0.app k ≫ ((frameEndpoint i).app k).hom at hv
  calc
    forwardFrame0.app k ≫
        (((frameEndpoint i).app k ≫
          daggerExtension X k f a₀ a₁ h₀ h₁).hom) =
      (boundaryLeg i k ≫ cylinderInclusion.app k ≫
        forwardFrame.app k) ≫
          (daggerExtension X k f a₀ a₁ h₀ h₁).hom := by
            rw [hv]
            rfl
    _ = (boundaryLeg i k ≫ cylinderInclusion.app k) ≫ f := by
          simp only [Category.assoc, daggerExtension_forward]
    _ = forwardFrame0.app k ≫ a.hom := hi

/-- A genuine dagger map has the prescribed forced reverse-copy restriction.
This is the uniqueness half of the proposed endpoint-cartesian square. -/
theorem reverse_restriction (X : DaggerSSet.{0}) (k : SimplexCategory)
    (g : frame1.obj k ⟶ X) :
    reverseFrame k ≫ g.hom =
      forcedReverse X k (forwardFrame.app k ≫ g.hom) := by
  let eS := DaggerSSet.daggerIso (frame1.obj k)
  let eT := DaggerSSet.daggerIso X
  have hcomm : eS.inv ≫ g.hom =
      SSet.opFunctor.map g.hom ≫ eT.inv := by
    apply (cancel_mono eT.hom).1
    calc
      (eS.inv ≫ g.hom) ≫ eT.hom =
          eS.inv ≫ (g.hom ≫ eT.hom) := Category.assoc _ _ _
      _ = eS.inv ≫ (eS.hom ≫ SSet.opFunctor.map g.hom) := by
          exact congrArg (fun q ↦ eS.inv ≫ q) g.comm
      _ = SSet.opFunctor.map g.hom := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = (SSet.opFunctor.map g.hom ≫ eT.inv) ≫ eT.hom := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change reverseFrame k ≫ g.hom =
    (𝟙 interval.op ⊗ₘ (GroupoidSimplexReversal.daggerParameter.obj k).dagger) ≫
      SSet.opFunctor.map (forwardFrame.app k ≫ g.hom) ≫ eT.inv
  rw [reverseFrame_calibration]
  simp only [Category.assoc]
  rw [hcomm]
  simp only [SSet.opFunctor.map_comp, Category.assoc]

/-- Once the ordinary forward copy is fixed, a dagger map on the original
outer-one frame is unique. The reverse copy is forced by its dagger. -/
theorem daggerExtension_unique (X : DaggerSSet.{0})
    (k : SimplexCategory) (f : intervalCylinder.obj k ⟶ X.toSSet)
    (a₀ a₁ : frame0.obj k ⟶ X)
    (h₀ : (boundaryLeg 0 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₀.hom)
    (h₁ : (boundaryLeg 1 k ≫ cylinderInclusion.app k) ≫ f =
      forwardFrame0.app k ≫ a₁.hom)
    (g : frame1.obj k ⟶ X)
    (hg : forwardFrame.app k ≫ g.hom = f) :
    g = daggerExtension X k f a₀ a₁ h₀ h₁ := by
  apply DaggerSSet.Hom.ext
  apply (frame_isPushout k).hom_ext
  · exact hg.trans (daggerExtension_forward X k f a₀ a₁ h₀ h₁).symm
  · rw [reverse_restriction X k g, hg]
    exact (reverse_underlyingExtension X k f a₀ a₁ h₀ h₁).symm

private theorem comparisonRow_endpoint_i (X : DaggerSSet.{0})
    (i : Fin 2) :
    (daggerNerve.obj X).map (vertex i).op ≫
        JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌ =
      JTRightAdjointOrderedFiber.comparisonRow X ⦋1⦌ ≫
        JTRightAdjointOrderedFiber.ordinaryRowEndpoint X.toSSet i := by
  apply NatTrans.ext
  funext k f
  have h := (JTUnderlyingRightComparison.comparison.app X).naturality
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (ordinaryEndpoint i, 𝟙 k.unop)))
  simpa [JTRightAdjointOrderedFiber.comparisonRow,
    JTRightAdjointOrderedFiber.ordinaryRowEndpoint,
    JTReversalInput.ordinaryInput, vertex,
    JTXiEndpointCollapseBoundary.ordinaryEndpoint] using congrFun h f

/-- The original comparison preserves the literal ordered endpoint
operators. This is the square whose cartesianness is proved below. -/
theorem endpoint_square (X : DaggerSSet.{0}) :
    JTRightAdjointOrderedFiber.daggerEndpointArrow X ≫
        prod.map
          (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌)
          (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌) =
      JTRightAdjointOrderedFiber.comparisonRow X ⦋1⦌ ≫
        JTRightAdjointOrderedFiber.ordinaryEndpointArrow X.toSSet := by
  apply prod.hom_ext
  · simpa only [JTRightAdjointOrderedFiber.daggerEndpointArrow,
      JTRightAdjointOrderedFiber.ordinaryEndpointArrow,
      prod.lift_fst, prod.lift_fst_assoc, prod.map_fst,
      Category.assoc] using comparisonRow_endpoint_i X 0
  · simpa only [JTRightAdjointOrderedFiber.daggerEndpointArrow,
      JTRightAdjointOrderedFiber.ordinaryEndpointArrow,
      prod.lift_snd, prod.lift_snd_assoc, prod.map_snd,
      Category.assoc] using comparisonRow_endpoint_i X 1

private theorem boundaryIota_std (i : Fin 2) :
    (if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ≫
        (SSet.boundary 1).ι =
      SSet.stdSimplex.map (ordinaryEndpoint i) := by
  fin_cases i
  · change SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι =
        SSet.stdSimplex.map (ordinaryEndpoint 0)
    rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
    apply SSet.yonedaEquiv.injective
    rfl
  · change SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι =
        SSet.stdSimplex.map (ordinaryEndpoint 1)
    rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
    apply SSet.yonedaEquiv.injective
    rfl

private theorem boundaryLeg_cylinderInclusion (i : Fin 2)
    (k : SimplexCategory) :
    boundaryLeg i k ≫ cylinderInclusion.app k =
      SSet.stdSimplex.map (ordinaryEndpoint i) ⊗ₘ
        𝟙 (GroupoidSimplex.parameter.obj k) := by
  change ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
      GroupoidSimplex.parameter.obj k) ≫
        ((SSet.boundary 1).ι ⊗ₘ
          𝟙 (GroupoidSimplex.parameter.obj k)) = _
  rw [MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_whiskerRight, boundaryIota_std i]
  simp only [MonoidalCategory.tensorHom_id]

private theorem comparisonRow_forward (X : DaggerSSet.{0})
    (m k : SimplexCategory)
    (f : frame.obj (ReverseSimplex.inclusion.obj m, k) ⟶ X) :
    (((JTRightAdjointOrderedFiber.comparisonRow X m).app (op k))
      (ULift.up f)).down = forwardPair.app (m, k) ≫ f.hom := by
  change (((JTUnderlyingRightComparison.comparison.app X).app (op (m, k)))
    (ULift.up f)).down = _
  simpa only [daggerGeneratorEquiv_eq_native] using
    JTRightAdjointForwardNormalization.comparison_on_represented_forward X m k f

private theorem ordinaryEndpoint_app (S : SSet.{0})
    (i : Fin 2) (k : SimplexCategory)
    (f : intervalCylinder.obj k ⟶ S) :
    (JTRightAdjointOrderedFiber.ordinaryRowEndpoint S i).app (op k)
        (ULift.up f) =
      ULift.up ((boundaryLeg i k ≫ cylinderInclusion.app k) ≫ f) := by
  have hb := boundaryLeg_cylinderInclusion i k
  change ULift.up
      ((SSet.stdSimplex.map (ordinaryEndpoint i) ⊗ₘ
          GroupoidSimplex.parameter.map (𝟙 k)) ≫ f) = _
  rw [GroupoidSimplex.parameter.map_id]
  rw [← hb]

/-- Each actual simplex degree of the original endpoint square is a
pullback of types. The inverse uses the dagger extension of its ordinary
forward component and the two specified dagger endpoint components. -/
private theorem endpoint_app_isPullback (X : DaggerSSet.{0})
    (q : SimplexCategoryᵒᵖ) :
    IsPullback
      ((JTRightAdjointOrderedFiber.comparisonRow X ⦋1⦌).app q)
      ((JTRightAdjointOrderedFiber.daggerEndpointArrow X).app q)
      ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow X.toSSet).app q)
      ((prod.map
        (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌)
        (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌)).app q) := by
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [NatTrans.comp_app] using
      (congr_app (endpoint_square X).symm q)
  · rintro ⟨a⟩ ⟨b⟩ ⟨hab, _⟩
    have h := congrArg ULift.down hab
    rw [comparisonRow_forward X ⦋1⦌ q.unop a,
      comparisonRow_forward X ⦋1⦌ q.unop b] at h
    have hf : forwardFrame.app q.unop ≫ a.hom =
        forwardFrame.app q.unop ≫ b.hom := h
    have heq : a = b := by
      apply DaggerSSet.Hom.ext
      apply (frame_isPushout q.unop).hom_ext
      · exact hf
      · rw [reverse_restriction X q.unop a,
          reverse_restriction X q.unop b, hf]
    exact congrArg ULift.up heq
  · intro u v huv
    rcases u with ⟨f⟩
    let D₀ := JTRightAdjointOrderedFiber.daggerRow X JTZeroObjects.zeroIndex
    let O₀ := JTRightAdjointOrderedFiber.ordinaryRow X.toSSet ⦋0⦌
    let a₀ : frame0.obj q.unop ⟶ X :=
      ((prod.fst : D₀ ⨯ D₀ ⟶ D₀).app q v).down
    let a₁ : frame0.obj q.unop ⟶ X :=
      ((prod.snd : D₀ ⨯ D₀ ⟶ D₀).app q v).down
    have h₀p := congrArg
      (fun z : (O₀ ⨯ O₀).obj q =>
        (prod.fst : O₀ ⨯ O₀ ⟶ O₀).app q z) huv
    have h₁p := congrArg
      (fun z : (O₀ ⨯ O₀).obj q =>
        (prod.snd : O₀ ⨯ O₀ ⟶ O₀).app q z) huv
    have h₀e :
        (JTRightAdjointOrderedFiber.ordinaryRowEndpoint X.toSSet 0).app q
            (ULift.up f) =
          (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌).app q
            (ULift.up a₀) := by
      change ((prod.lift
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint X.toSSet 0)
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint X.toSSet 1) ≫
            prod.fst).app q) (ULift.up f) =
        ((prod.map (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌)
          (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌) ≫
            prod.fst).app q) v at h₀p
      rw [prod.lift_fst, prod.map_fst] at h₀p
      exact h₀p
    have h₁e :
        (JTRightAdjointOrderedFiber.ordinaryRowEndpoint X.toSSet 1).app q
            (ULift.up f) =
          (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌).app q
            (ULift.up a₁) := by
      change ((prod.lift
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint X.toSSet 0)
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint X.toSSet 1) ≫
            prod.snd).app q) (ULift.up f) =
        ((prod.map (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌)
          (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌) ≫
            prod.snd).app q) v at h₁p
      rw [prod.lift_snd, prod.map_snd] at h₁p
      exact h₁p
    have h₀ : (boundaryLeg 0 q.unop ≫
        cylinderInclusion.app q.unop) ≫ f =
          forwardFrame0.app q.unop ≫ a₀.hom := by
      have h := congrArg ULift.down h₀e
      rw [ordinaryEndpoint_app X.toSSet 0 q.unop f,
        comparisonRow_forward X ⦋0⦌ q.unop a₀] at h
      exact h
    have h₁ : (boundaryLeg 1 q.unop ≫
        cylinderInclusion.app q.unop) ≫ f =
          forwardFrame0.app q.unop ≫ a₁.hom := by
      have h := congrArg ULift.down h₁e
      rw [ordinaryEndpoint_app X.toSSet 1 q.unop f,
        comparisonRow_forward X ⦋0⦌ q.unop a₁] at h
      exact h
    let g := daggerExtension X q.unop f a₀ a₁ h₀ h₁
    refine ⟨ULift.up g, ?_, ?_⟩
    · apply ULift.ext
      exact (comparisonRow_forward X ⦋1⦌ q.unop g).trans
        (daggerExtension_forward X q.unop f a₀ a₁ h₀ h₁)
    · let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj q
      letI : PreservesLimit (pair D₀ D₀) E :=
        evaluation_preservesLimit (pair D₀ D₀) q
      let e := PreservesLimitPair.iso E D₀ D₀ ≪≫
        Types.binaryProductIso (E.obj D₀) (E.obj D₀)
      have e_fst : e.hom ≫ Prod.fst =
          (prod.fst : D₀ ⨯ D₀ ⟶ D₀).app q := by
        dsimp only [e, Iso.trans_hom]
        rw [Category.assoc, Types.binaryProductIso_hom_comp_fst,
          PreservesLimitPair.iso_hom, prodComparison_fst]
        rfl
      have e_snd : e.hom ≫ Prod.snd =
          (prod.snd : D₀ ⨯ D₀ ⟶ D₀).app q := by
        dsimp only [e, Iso.trans_hom]
        rw [Category.assoc, Types.binaryProductIso_hom_comp_snd,
          PreservesLimitPair.iso_hom, prodComparison_snd]
        rfl
      apply e.toEquiv.injective
      apply Prod.ext
      · change Prod.fst (e.hom
          ((JTRightAdjointOrderedFiber.daggerEndpointArrow X).app q
            (ULift.up g))) = Prod.fst (e.hom v)
        change (e.hom ≫ Prod.fst)
            ((JTRightAdjointOrderedFiber.daggerEndpointArrow X).app q
              (ULift.up g)) = (e.hom ≫ Prod.fst) v
        rw [e_fst]
        change ((prod.fst : D₀ ⨯ D₀ ⟶ D₀).app q)
          ((JTRightAdjointOrderedFiber.daggerEndpointArrow X).app q
            (ULift.up g)) =
            (prod.fst : D₀ ⨯ D₀ ⟶ D₀).app q v
        change ((JTRightAdjointOrderedFiber.daggerEndpointArrow X ≫
          prod.fst).app q) (ULift.up g) =
            (prod.fst : D₀ ⨯ D₀ ⟶ D₀).app q v
        rw [JTRightAdjointOrderedFiber.daggerEndpointArrow, prod.lift_fst]
        change ULift.up ((frameEndpoint 0).app q.unop ≫ g) =
          (prod.fst : D₀ ⨯ D₀ ⟶ D₀).app q v
        calc
          _ = ULift.up a₀ := congrArg ULift.up
            (daggerExtension_endpoint X 0 q.unop f a₀ a₁ h₀ h₁ a₀ h₀)
          _ = _ := ULift.up_down _
      · change Prod.snd (e.hom
          ((JTRightAdjointOrderedFiber.daggerEndpointArrow X).app q
            (ULift.up g))) = Prod.snd (e.hom v)
        change (e.hom ≫ Prod.snd)
            ((JTRightAdjointOrderedFiber.daggerEndpointArrow X).app q
              (ULift.up g)) = (e.hom ≫ Prod.snd) v
        rw [e_snd]
        change ((prod.snd : D₀ ⨯ D₀ ⟶ D₀).app q)
          ((JTRightAdjointOrderedFiber.daggerEndpointArrow X).app q
            (ULift.up g)) =
            (prod.snd : D₀ ⨯ D₀ ⟶ D₀).app q v
        change ((JTRightAdjointOrderedFiber.daggerEndpointArrow X ≫
          prod.snd).app q) (ULift.up g) =
            (prod.snd : D₀ ⨯ D₀ ⟶ D₀).app q v
        rw [JTRightAdjointOrderedFiber.daggerEndpointArrow, prod.lift_snd]
        change ULift.up ((frameEndpoint 1).app q.unop ≫ g) =
          (prod.snd : D₀ ⨯ D₀ ⟶ D₀).app q v
        calc
          _ = ULift.up a₁ := congrArg ULift.up
            (daggerExtension_endpoint X 1 q.unop f a₀ a₁ h₀ h₁ a₁ h₁)
          _ = _ := ULift.up_down _

/-- The original underlying right-adjoint comparison is cartesian over the
full ordered endpoint pair, for every dagger simplicial set. The proof uses
the actual two-copy represented frame and all simplex degrees. -/
theorem endpoint_isPullback (X : DaggerSSet.{0}) :
    IsPullback
      (JTRightAdjointOrderedFiber.comparisonRow X ⦋1⦌)
      (JTRightAdjointOrderedFiber.daggerEndpointArrow X)
      (JTRightAdjointOrderedFiber.ordinaryEndpointArrow X.toSSet)
      (prod.map
        (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌)
        (JTRightAdjointOrderedFiber.comparisonRow X ⦋0⦌)) := by
  let c := PullbackCone.mk
    (JTRightAdjointOrderedFiber.comparisonRow X ⦋1⦌)
    (JTRightAdjointOrderedFiber.daggerEndpointArrow X)
    (endpoint_square X).symm
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro q
  let h := endpoint_app_isPullback X q
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

end

end DaggerModels.PartII.JTRightEndpointCartesian
