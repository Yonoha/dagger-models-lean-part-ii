import NativeWalkingPositiveBoundaryPushout
import NativeWalkingEndpointSection
import NativeBoundaryJoyalMappingWeak
import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions
import TopCatModelCategory.SSet.Monoidal
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# Relative walking-isomorphism cylinder lifting

An inner fibration lifts the positive standard-boundary pushout tensors
with the literal chosen zero vertex of the native walking isomorphism.
The zero-dimensional boundary tensor is the chosen zero inclusion itself,
up to its actual pushout and simplex-zero unitors.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial MonoidalCategory
  HomotopicalAlgebra MorphismProperty
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerNativeWalkingMonoPushout
open DaggerNativeWalkingPositiveBoundaryPushout
open DaggerNativeInnerHornFactorization
open DaggerNativeBoundaryJoyalMappingWeak
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerNativeOrdinaryInnerIsoRelativeCylinder

noncomputable section

variable {E B : SSet.{u}} (p : E ⟶ B)

private def pb : SSet.PullbackIhom zeroInclusion.{u} p :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

/-- Every positive standard boundary lifts against the exact relative
internal-Hom projection under only the native inner-fibration premise. -/
theorem positive_boundary_lifting
    (hp : innerFibrations p) (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} (n + 1)).ι (pb p).π := by
  let sq := relativePushout (SSet.boundary.{u} (n + 1)).ι
  rw [← SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom
    sq.flip (pb p),
    HasLiftingProperty.iff_of_arrow_iso_left sq.flipArrowIso]
  exact canonical_inner n p hp

private local instance : BraidedCategory SSet.{u} :=
  .ofCartesianMonoidalCategory

private local instance (K : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (tensorLeft K) :=
  (ihom.adjunction K).leftAdjoint_preservesColimits

private local instance (K : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (tensorRight K) :=
  ⟨fun {J} _ ↦ by
    letI : PreservesColimitsOfShape J (tensorLeft K) := inferInstance
    exact preservesColimitsOfShape_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight K)⟩

private def zeroBox :
    SSet.PushoutTensor (SSet.boundary.{u} 0).ι zeroInclusion.{u} :=
  relativePushout (SSet.boundary.{u} 0).ι

private theorem zeroBox_inl_iso : IsIso (zeroBox.{u}.inl) := by
  have hI₁ : IsInitial
      ((SSet.boundary.{u} 0).toSSet ⊗ (Δ[0] : SSet.{u})) :=
    (SSet.boundary.isInitial.{u}).isInitialObj
      (tensorRight (Δ[0] : SSet.{u}))
  have hI₂ : IsInitial
      ((SSet.boundary.{u} 0).toSSet ⊗ J.{u}) :=
    (SSet.boundary.isInitial.{u}).isInitialObj (tensorRight J.{u})
  have h : IsIso
      ((SSet.boundary.{u} 0).toSSet ◁ zeroInclusion.{u}) := by
    let e := hI₁.uniqueUpToIso hI₂
    have he : (SSet.boundary.{u} 0).toSSet ◁ zeroInclusion.{u} =
        e.hom := hI₁.hom_ext _ _
    rw [he]
    infer_instance
  letI : IsIso (((curriedTensor SSet.{u}).obj
      (SSet.boundary.{u} 0).toSSet).map zeroInclusion.{u}) := by
    change IsIso ((SSet.boundary.{u} 0).toSSet ◁ zeroInclusion.{u})
    exact h
  exact zeroBox.{u}.isPushout.isIso_inl_of_isIso

/-- The zero-boundary pushout tensor is isomorphic as an arrow to the
original native selected-zero inclusion. -/
private def zeroBoxArrowIso :
    Arrow.mk zeroBox.{u}.ι ≅ Arrow.mk zeroInclusion.{u} := by
  letI : IsIso zeroBox.{u}.inl := zeroBox_inl_iso
  let s := (asIso zeroBox.{u}.inl).symm ≪≫
    SSet.stdSimplex.leftUnitor (Δ[0] : SSet.{u})
  let t := SSet.stdSimplex.leftUnitor J.{u}
  refine Arrow.isoMk s t ?_
  change s.hom ≫ zeroInclusion.{u} = zeroBox.{u}.ι ≫ t.hom
  have h := zeroBox.{u}.inl_ι
  change zeroBox.{u}.inl ≫ zeroBox.{u}.ι =
    (Δ[0] : SSet.{u}) ◁ zeroInclusion.{u} at h
  calc
    s.hom ≫ zeroInclusion.{u} =
      (asIso zeroBox.{u}.inl).inv ≫
        (SSet.stdSimplex.leftUnitor (Δ[0] : SSet.{u})).hom ≫
          zeroInclusion.{u} := rfl
    _ = (asIso zeroBox.{u}.inl).inv ≫
        ((Δ[0] : SSet.{u}) ◁ zeroInclusion.{u}) ≫ t.hom := by
          rw [SSet.stdSimplex.leftUnitor_hom_naturality]
    _ = (asIso zeroBox.{u}.inl).inv ≫
        (zeroBox.{u}.inl ≫ zeroBox.{u}.ι) ≫ t.hom := by rw [h]
    _ = zeroBox.{u}.ι ≫ t.hom := by
      change ((asIso zeroBox.{u}.inl).inv ≫
          (asIso zeroBox.{u}.inl).hom) ≫ zeroBox.{u}.ι ≫ t.hom =
        zeroBox.{u}.ι ≫ t.hom
      simp only [Iso.inv_hom_id, Category.id_comp]

/-- The zero boundary lifts against the same relative internal-Hom
projection exactly when the original zero inclusion lifts against p. -/
theorem zero_boundary_lifting
    (hzero : HasLiftingProperty zeroInclusion.{u} p) :
    HasLiftingProperty (SSet.boundary.{u} 0).ι (pb p).π := by
  rw [← SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom
    zeroBox.{u}.flip (pb p),
    HasLiftingProperty.iff_of_arrow_iso_left zeroBox.{u}.flipArrowIso]
  exact (HasLiftingProperty.iff_of_arrow_iso_left zeroBoxArrowIso p).mpr hzero

/-- Every standard boundary lifts against the exact relative internal-Hom
projection when `p` is an inner fibration lifting the selected zero vertex. -/
theorem boundary_lifting
    (hp : innerFibrations p)
    (hzero : HasLiftingProperty zeroInclusion.{u} p)
    (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι (pb p).π := by
  cases n with
  | zero => exact zero_boundary_lifting p hzero
  | succ n => exact positive_boundary_lifting p hp n

/-- The native walking-isomorphism cylinder against any monomorphism lifts
against the original inner fibration. The target arrow is the actual `p`. -/
theorem mono_pushout_zero_lifting
    (hp : innerFibrations p)
    (hzero : HasLiftingProperty zeroInclusion.{u} p)
    {A D : SSet.{u}} (i : A ⟶ D) [Mono i]
    (sq : SSet.PushoutTensor i zeroInclusion.{u}) :
    HasLiftingProperty sq.ι p := by
  have hm : (MorphismProperty.monomorphisms SSet.{u}).rlp (pb p).π :=
    boundary_rlp_monomorphisms (pb p).π (boundary_lifting p hp hzero)
  have hi : HasLiftingProperty i (pb p).π :=
    hm _ (MorphismProperty.monomorphisms.infer_property i)
  have hflip : HasLiftingProperty sq.flip.ι p :=
    (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom
      sq.flip (pb p)).mpr hi
  exact (HasLiftingProperty.iff_of_arrow_iso_left sq.flipArrowIso p).mp hflip

#print axioms positive_boundary_lifting
#print axioms zero_boundary_lifting
#print axioms mono_pushout_zero_lifting

end

end DaggerNativeOrdinaryInnerIsoRelativeCylinder
