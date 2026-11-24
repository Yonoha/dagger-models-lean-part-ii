import OrdinaryJTMappingFrameWeak
import NativeStandardSpineInner

/-!
# Spine restriction in the literal ordinary JT right nerve

The public native row/Hom isomorphism identifies each original right-nerve row
with Hom from the same product weight. Restriction to the standard spine is
Kan weak into any quasicategory, by ordinary Joyal weakness of the spine and
the checked mapping-frame theorem. No locality hypothesis on an input W or
weakness of its derived-unit map is assumed or asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MonoidalCategory DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTRightNerveSegal

noncomputable section

/-- The represented ordinary row uses exactly the tensor weight with constant first factor. -/
private theorem standardFrame_eq (m : SimplexCategory) :
    CategoryTheory.Prod.sectR m SimplexCategory ⋙ OrdinaryJTRealization.tFunctor =
      OrdinaryJTMappingFrameWeak.frame (SSet.stdSimplex.obj m) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro k l θ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change SSet.stdSimplex.map (𝟙 m) ⊗ₘ GroupoidSimplex.parameter.map θ =
    SSet.stdSimplex.obj m ◁ GroupoidSimplex.parameter.map θ
  have hm : SSet.stdSimplex.map (𝟙 m) = 𝟙 (SSet.stdSimplex.obj m) :=
    SSet.stdSimplex.map_id m
  rw [hm, MonoidalCategory.id_tensorHom]

/-- The literal ordinary right-nerve row, with only its native universe lift removed. -/
def rowMappingIso (X : SSet.{0}) (m : SimplexCategory) :
    JTRightAdjointOrderedFiber.ordinaryRow X m ≅
      OrdinaryJTMappingFrameWeak.mapping X (SSet.stdSimplex.obj m) :=
  JTRightAdjointOrderedFiber.ordinaryRowHomIso X m ≪≫
    eqToIso (congrArg
      (fun F : SimplexCategory ⥤ SSet.{0} ↦ EndpointMappingFiber.mapping (Z := X) F)
      (standardFrame_eq m))

/-- Restrict the original nth row along the literal full standard spine inclusion. -/
def spineRestriction (X : SSet.{0}) (n : ℕ) :
    JTRightAdjointOrderedFiber.ordinaryRow X ⦋n⦌ ⟶
      OrdinaryJTMappingFrameWeak.mapping X
        (DaggerNativeStandardSpineInner.spine n).toSSet :=
  (rowMappingIso X ⦋n⦌).hom ≫
    OrdinaryJTMappingFrameWeak.restriction X (DaggerNativeStandardSpineInner.spine n).ι

/-- The actual ordinary JT right-nerve spine restriction is Kan weak for every
quasicategory and every degree, including the zero and one degrees. -/
theorem spineRestriction_weak (X : SSet.{0}) [X.Quasicategory] (n : ℕ) :
    DaggerSSetGluing.GW (spineRestriction X n) := by
  letI : WeakEquivalence
      (OrdinaryJTMappingFrameWeak.restriction X
        (DaggerNativeStandardSpineInner.spine n).ι) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (OrdinaryJTMappingFrameWeak.restriction_weak X
        (DaggerNativeStandardSpineInner.spine n).ι
        (DaggerNativeStandardSpineInner.inclusion_categorical_weak n))
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  change WeakEquivalence ((rowMappingIso X ⦋n⦌).hom ≫
    OrdinaryJTMappingFrameWeak.restriction X (DaggerNativeStandardSpineInner.spine n).ι)
  infer_instance

#print axioms rowMappingIso
#print axioms spineRestriction_weak

end
end DaggerModels.PartII.OrdinaryJTRightNerveSegal
