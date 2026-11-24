import DaggerModelsPartII.JTEndpointCobase
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.HomCongr

/-!
# Hom maps out of an actual endpoint cobase

The native pushout/precomposition adjunction identifies maps under the fixed
endpoint object with maps from the original frame satisfying its endpoint
square. The pushout symmetry accounts for the manuscript's B-first convention.
-/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

universe v u
namespace DaggerModels.PartII.EndpointCobaseHom

noncomputable section

variable {C : Type u} [Category.{v} C] [HasPushouts C]

/-- The actual B-first pushout is the native undercategory cobase, with
its endpoint inclusion fixed by pushout symmetry. -/
def cobaseUnderIso {S T B : C} (u : S ⟶ T) (a : S ⟶ B) :
    Under.mk (pushout.inl a u) ≅ (Under.pushout a).obj (Under.mk u) :=
  Under.isoMk (pushoutSymmetry a u) (by simp)

/-- Under morphisms are exactly underlying maps with the literal triangle. -/
def underHomEquiv {B T X : C} (u : B ⟶ T) (b : B ⟶ X) :
    (Under.mk u ⟶ Under.mk b) ≃ {f : T ⟶ X // u ≫ f = b} where
  toFun f := ⟨f.right, Under.w f⟩
  invFun f := Under.homMk f.val f.property
  left_inv f := by ext; rfl
  right_inv f := by apply Subtype.ext; rfl

/-- The exact endpoint-cobase Hom equivalence, with no model or fibrancy
hypothesis. Both triangles use the given endpoint map b. -/
def cobaseHomEquiv {S T B X : C} (u : S ⟶ T) (a : S ⟶ B) (b : B ⟶ X) :
    (Under.mk (pushout.inl a u) ⟶ Under.mk b) ≃
      {f : T ⟶ X // u ≫ f = a ≫ b} :=
  (Iso.homCongr (cobaseUnderIso u a) (Iso.refl (Under.mk b))).trans
    (((Under.mapPushoutAdj a).homEquiv (Under.mk u) (Under.mk b)).trans
      (underHomEquiv u (a ≫ b)))

/-- The forward equivalence is restriction along the actual frame inclusion. -/
theorem cobaseHomEquiv_val {S T B X : C} (u : S ⟶ T) (a : S ⟶ B) (b : B ⟶ X)
    (f : Under.mk (pushout.inl a u) ⟶ Under.mk b) :
    (cobaseHomEquiv u a b f).val = pushout.inr a u ≫ f.right := by
  simp only [cobaseHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  simp only [Under.mapPushoutAdj, Adjunction.mkOfHomEquiv_homEquiv]
  change pushout.inl u a ≫ ((cobaseUnderIso u a).inv.right ≫ f.right) = _
  simp [cobaseUnderIso]

/-- The inverse is the unique pushout extension with endpoint restriction b. -/
theorem cobaseHomEquiv_symm_right {S T B X : C} (u : S ⟶ T) (a : S ⟶ B)
    (b : B ⟶ X) (f : {g : T ⟶ X // u ≫ g = a ≫ b}) :
    ((cobaseHomEquiv u a b).symm f).right =
      pushout.desc b f.val f.property.symm := by
  apply pushout.hom_ext
  · have h := Under.w ((cobaseHomEquiv u a b).symm f)
    simpa only [Under.mk_hom, pushout.inl_desc] using h
  · have h := cobaseHomEquiv_val u a b ((cobaseHomEquiv u a b).symm f)
    rw [Equiv.apply_symm_apply] at h
    simpa only [pushout.inr_desc] using h.symm

end

end DaggerModels.PartII.EndpointCobaseHom
