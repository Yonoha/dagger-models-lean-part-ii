import DaggerModelsPartII.JTPrismSubcomplexExtension
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv
import NativeIhomRelativeSectionsWeak

/-!
# Relative extension when a prism meets a subcomplex along a time subobject
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTPrismTimeFaceExtension

open SSet.Subcomplex
open JTFixedLiftSpaceTimeEquiv

noncomputable section

variable {B T K : SSet.{u}} (f : B ⊗ T ⟶ K)
variable (F : K.Subcomplex) (C : T.Subcomplex)
variable (hf : F.preimage f = (⊤ : B.Subcomplex).prod C)

private theorem range_whisker :
    range (B ◁ C.ι) = (⊤ : B.Subcomplex).prod C := by
  rw [show B ◁ C.ι = (𝟙 B) ⊗ₘ C.ι from rfl, range_tensorHom, range_eq_top]
  exact congrArg ((⊤ : B.Subcomplex).prod) (SSet.Subcomplex.range_ι C)

/-- Identify the entire overlap with the product over the time subobject. -/
def preimageIso : B ⊗ C.toSSet ≅ (F.preimage f).toSSet := by
  haveI := DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono B C.ι
  exact asIso (toRange (B ◁ C.ι)) ≪≫
    SSet.Subcomplex.eqToIso ((range_whisker C).trans hf.symm)

@[reassoc]
theorem preimageIso_ι : (preimageIso f F C hf).hom ≫ (F.preimage f).ι = B ◁ C.ι := by
  simp [preimageIso, Category.assoc]

/-- The overlap identifications commute with inclusions of the entire time subobjects. -/
theorem preimageIso_natural {F' : K.Subcomplex} {C' : T.Subcomplex}
    (hf' : F'.preimage f = (⊤ : B.Subcomplex).prod C')
    (hF : F' ≤ F) (hC : C' ≤ C) :
    (B ◁ SSet.Subcomplex.homOfLE hC) ≫ (preimageIso f F C hf).hom =
      (preimageIso f F' C' hf').hom ≫ SSet.Subcomplex.homOfLE
        (show F'.preimage f ≤ F.preimage f from fun a ↦ Set.preimage_mono (hF a)) := by
  apply (cancel_mono (F.preimage f).ι).1
  rw [Category.assoc, preimageIso_ι, Category.assoc, homOfLE_ι, preimageIso_ι,
    ← whiskerLeft_comp, homOfLE_ι]

/-- Extend a map given on the enlarged time subcomplex, retaining it
exactly and keeping the original fixed-square equations on the full prism. -/
theorem exists_extension [Mono f] [WeakEquivalence f]
    (hw : WeakEquivalence (F.fromPreimage f))
    {A X Y : SSet.{u}} {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
    (sq : CommSq t i p b) [Mono i] [WeakEquivalence i] [Fibration p]
    (q : K ⟶ Y) (hbase : f ≫ q = fst B T ≫ b)
    (G : F.toSSet ⟶ X) (hG : G ≫ p = F.ι ≫ q)
    (hstat : (i ▷ C.toSSet) ≫ (preimageIso f F C hf).hom ≫ F.fromPreimage f ≫ G =
      fst A C.toSSet ≫ t) :
    ∃ L : K ⟶ X, F.ι ≫ L = G ∧ L ≫ p = q ∧ (i ▷ T) ≫ f ≫ L = fst A T ≫ t := by
  let P := (preimageIso f F C hf).hom
  let v := P ≫ F.fromPreimage f ≫ G
  have hv : v ≫ p = fst B C.toSSet ≫ b := by
    change (P ≫ F.fromPreimage f ≫ G) ≫ p = _
    rw [Category.assoc, Category.assoc, hG, fromPreimage_ι_assoc,
      ← Category.assoc P, preimageIso_ι, hbase, whiskerLeft_fst_assoc]
  obtain ⟨w, hrestrict, hstation, hwp⟩ := exists_extend_time sq C.ι v hstat hv
  have hc : (F.preimage f).ι ≫ w = F.fromPreimage f ≫ G := by
    apply (cancel_epi P).1
    rw [← Category.assoc, preimageIso_ι, hrestrict]
  obtain ⟨L, hL, hFL, hLp⟩ := JTPrismSubcomplexExtension.exists_extension f F hw
    q w G (hwp.trans hbase.symm) hG hc
  refine ⟨L, hFL, hLp, ?_⟩
  rw [hL]
  exact hstation

end

end DaggerModels.PartII.JTPrismTimeFaceExtension
