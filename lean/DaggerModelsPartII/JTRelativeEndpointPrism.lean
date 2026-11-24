import SSetSM7
import NativeKanTrivialCofibrationRestriction

/-!
# Relative ordinary cylinder lifting

The native pushout tensor imposes the two full time faces and the
stationary chosen vertex before lifting in the ordinary Kan model.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTRelativeEndpointPrism

noncomputable section

/-- The native pushout tensor for the selected vertex and the two time faces. -/
def relativeCylinderSquare {A B : SSet.{u}} (i : A ⟶ B) :
    SSet.PushoutTensor i (SSet.boundary 1).ι :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- A Kan weak monomorphism has the left lifting property after taking its
pushout tensor with the two endpoint inclusion.  The Kan model is essential:
an ordinary vertex of a simplex is generally not a Joyal weak equivalence. -/
theorem relativeCylinderSquare_lifts {A B X Y : SSet.{u}}
    (i : A ⟶ B) [Mono i] [WeakEquivalence i]
    (p : X ⟶ Y) [Fibration p] :
    HasLiftingProperty (relativeCylinderSquare i).ι p := by
  letI : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  have hi : SSet.anodyneExtensions i :=
    DaggerNativeKanTrivialCofibrationRestriction.trivial_anodyne i
  have hs : SSet.anodyneExtensions (relativeCylinderSquare i).ι :=
    SSet.anodyneExtensions.pushoutTensorι₁ (relativeCylinderSquare i) hi
  exact hs.hasLeftLiftingProperty p

/-- The exact model-category extension step.  Here `gB` is the prescribed
map on `B ⊗ ∂Δ[1]`, and `gA` is the constant map on `A ⊗ Δ[1]`.
The equations `hB` and `hA` encode the fixed base simplex. -/
theorem exists_relativePrism_of_boundary
    {A B X Y : SSet.{u}} (i : A ⟶ B)
    [Mono i] [WeakEquivalence i]
    (p : X ⟶ Y) [Fibration p]
    (bottom : B ⊗ (Δ[1] : SSet.{u}) ⟶ Y)
    (gB : B ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ X)
    (gA : A ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (hcompat : (i ▷ (SSet.boundary 1 : SSet.{u})) ≫ gB =
      (A ◁ (SSet.boundary 1).ι) ≫ gA)
    (hB : gB ≫ p = (B ◁ (SSet.boundary 1).ι) ≫ bottom)
    (hA : gA ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ bottom) :
    ∃ F : B ⊗ (Δ[1] : SSet.{u}) ⟶ X,
      (relativeCylinderSquare i).inl ≫
        (relativeCylinderSquare i).ι ≫ F = gB ∧
      (relativeCylinderSquare i).inr ≫
        (relativeCylinderSquare i).ι ≫ F = gA ∧
      F ≫ p = bottom := by
  let sq := relativeCylinderSquare i
  let top : sq.pt ⟶ X := sq.isPushout.desc gB gA hcompat
  have htop : top ≫ p = sq.ι ≫ bottom := by
    apply sq.isPushout.hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc,
        ← Category.assoc, sq.inl_ι]
      exact hB
    · rw [← Category.assoc, IsPushout.inr_desc,
        ← Category.assoc, sq.inr_ι]
      exact hA
  letI : HasLiftingProperty sq.ι p :=
    relativeCylinderSquare_lifts i p
  let c : CommSq top sq.ι p bottom := ⟨htop⟩
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · change sq.inl ≫ sq.ι ≫ c.lift = gB
    rw [c.fac_left]
    exact sq.isPushout.inl_desc gB gA hcompat
  · change sq.inr ≫ sq.ι ≫ c.lift = gA
    rw [c.fac_left]
    exact sq.isPushout.inr_desc gB gA hcompat

/-- Our time slice is the actual ordered boundary component, transported
through the standard right unitor. -/
def timeSlice (B : SSet.{u}) (t : Fin 2) :
    B ⟶ B ⊗ (Δ[1] : SSet.{u}) :=
  (SSet.stdSimplex.rightUnitor B).inv ≫
    (B ◁ (if t = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁)) ≫
      (B ◁ (SSet.boundary 1).ι)

/-- The two prescribed endpoint maps glued on `B ⊗ ∂Δ[1]`. -/
def endpointBoundary {B X : SSet.{u}}
    (e0 e1 : B ⟶ X) :
    B ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ X :=
  (BinaryCofan.IsColimit.desc' (SSet.boundary₁.isColimitLeftTensor B)
    (fst B (Δ[0] : SSet.{u}) ≫ e0)
    (fst B (Δ[0] : SSet.{u}) ≫ e1)).1

theorem endpointBoundary_zero {B X : SSet.{u}}
    (e0 e1 : B ⟶ X) :
    (B ◁ SSet.boundary₁.ι₀) ≫ endpointBoundary e0 e1 =
      fst B (Δ[0] : SSet.{u}) ≫ e0 :=
  (BinaryCofan.IsColimit.desc' (SSet.boundary₁.isColimitLeftTensor B)
    (fst B (Δ[0] : SSet.{u}) ≫ e0)
    (fst B (Δ[0] : SSet.{u}) ≫ e1)).2.1

theorem endpointBoundary_one {B X : SSet.{u}}
    (e0 e1 : B ⟶ X) :
    (B ◁ SSet.boundary₁.ι₁) ≫ endpointBoundary e0 e1 =
      fst B (Δ[0] : SSet.{u}) ≫ e1 :=
  (BinaryCofan.IsColimit.desc' (SSet.boundary₁.isColimitLeftTensor B)
    (fst B (Δ[0] : SSet.{u}) ≫ e0)
    (fst B (Δ[0] : SSet.{u}) ≫ e1)).2.2

/-- The full relative prism with both prescribed time faces, a stationary
selected vertex, and the fixed base simplex.  The hypotheses `[WeakEquivalence i]`
and `[Fibration p]` refer to the ordinary Kan model. -/
theorem exists_relativePrism
    {A B X Y : SSet.{u}} (i : A ⟶ B)
    [Mono i] [WeakEquivalence i]
    (p : X ⟶ Y) [Fibration p]
    (b : B ⟶ Y) (t : A ⟶ X)
    (e0 e1 : B ⟶ X)
    (he0 : e0 ≫ p = b) (he1 : e1 ≫ p = b)
    (hi0 : i ≫ e0 = t) (hi1 : i ≫ e1 = t) :
    ∃ F : B ⊗ (Δ[1] : SSet.{u}) ⟶ X,
      timeSlice B 0 ≫ F = e0 ∧
      timeSlice B 1 ≫ F = e1 ∧
      (i ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ F =
        fst A (Δ[1] : SSet.{u}) ≫ t ∧
      F ≫ p = fst B (Δ[1] : SSet.{u}) ≫ b := by
  let gB := endpointBoundary e0 e1
  let gA := fst A (Δ[1] : SSet.{u}) ≫ t
  let bottom := fst B (Δ[1] : SSet.{u}) ≫ b
  have hcompat :
      (i ▷ (SSet.boundary 1 : SSet.{u})) ≫ gB =
        (A ◁ (SSet.boundary 1).ι) ≫ gA := by
    apply SSet.boundary₁.hom_ext_leftTensor
    · rw [MonoidalCategory.whisker_exchange_assoc,
        endpointBoundary_zero]
      apply NatTrans.ext
      funext q x
      exact congrFun (NatTrans.congr_app hi0 q) x.1
    · rw [MonoidalCategory.whisker_exchange_assoc,
        endpointBoundary_one]
      apply NatTrans.ext
      funext q x
      exact congrFun (NatTrans.congr_app hi1 q) x.1
  have hB : gB ≫ p = (B ◁ (SSet.boundary 1).ι) ≫ bottom := by
    apply SSet.boundary₁.hom_ext_leftTensor
    · change (B ◁ SSet.boundary₁.ι₀) ≫ endpointBoundary e0 e1 ≫ p = _
      rw [← Category.assoc, endpointBoundary_zero, Category.assoc, he0]
      apply NatTrans.ext
      rfl
    · change (B ◁ SSet.boundary₁.ι₁) ≫ endpointBoundary e0 e1 ≫ p = _
      rw [← Category.assoc, endpointBoundary_one, Category.assoc, he1]
      apply NatTrans.ext
      rfl
  have htp : t ≫ p = i ≫ b := by
    calc
      t ≫ p = (i ≫ e0) ≫ p := by rw [hi0]
      _ = i ≫ b := by rw [Category.assoc, he0]
  have hA : gA ≫ p =
      (i ▷ (Δ[1] : SSet.{u})) ≫ bottom := by
    dsimp [gA, bottom]
    rw [Category.assoc, htp, ← Category.assoc,
      CartesianMonoidalCategory.whiskerRight_fst_assoc, Category.assoc]
  obtain ⟨F, hFB, hFA, hFp⟩ :=
    exists_relativePrism_of_boundary i p bottom gB gA hcompat hB hA
  have hFB' : (B ◁ (SSet.boundary 1).ι) ≫ F = gB := by
    rw [← Category.assoc, (relativeCylinderSquare i).inl_ι] at hFB
    exact hFB
  have hFA' : (i ▷ (Δ[1] : SSet.{u})) ≫ F = gA := by
    rw [← Category.assoc, (relativeCylinderSquare i).inr_ι] at hFA
    exact hFA
  refine ⟨F, ?_, ?_, ?_, hFp⟩
  · change (SSet.stdSimplex.rightUnitor B).inv ≫
      (B ◁ SSet.boundary₁.ι₀) ≫
        (B ◁ (SSet.boundary 1).ι) ≫ F = e0
    rw [hFB']
    change _ ≫ (B ◁ SSet.boundary₁.ι₀) ≫ endpointBoundary e0 e1 = e0
    rw [endpointBoundary_zero, ← Category.assoc, SSet.stdSimplex.rightUnitor_inv_fst,
      Category.id_comp]
  · change (SSet.stdSimplex.rightUnitor B).inv ≫
      (B ◁ SSet.boundary₁.ι₁) ≫
        (B ◁ (SSet.boundary 1).ι) ≫ F = e1
    rw [hFB']
    change _ ≫ (B ◁ SSet.boundary₁.ι₁) ≫ endpointBoundary e0 e1 = e1
    rw [endpointBoundary_one, ← Category.assoc, SSet.stdSimplex.rightUnitor_inv_fst,
      Category.id_comp]
  · simpa only [MonoidalCategory.tensorHom_id] using hFA'

end

end DaggerModels.PartII.JTRelativeEndpointPrism
