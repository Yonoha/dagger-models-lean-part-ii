import OrdinaryCSSConditions
import OrdinaryDiscreteMapping
import OrdinaryJTHorizontalMapping
import OrdinarySpaceReedyInjective
import OrdinaryJTRightNerveCompleteness

/-!
# Ordinary CSS locality of the actual JT right adjoint

The two checked mapping comparisons identify each actual discrete-diagram
mapping test with the unchanged `K × J[•]` mapping frame. Original Joyal
weakness of the ordinary spine and walking-isomorphism vertex therefore
proves strict ordinary CSS locality, with no condition on a dagger input.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTLocality

open OrdinaryCSSLocalization (Space)
open OrdinaryJTCurriedAdjunction (right)

noncomputable section

private local instance : ModelCategory Space :=
  OrdinarySpaceReedyInjective.injectiveModel

/-- The actual right adjoint is fibrant in the injective Kan base model. -/
theorem right_obj_base_isFibrant (X : SSet.{0}) [X.Quasicategory] :
    IsFibrant (right.obj X) := by
  have hp : OrdinarySpaceReedyInjective.reedyModel.categoryWithFibrations.fibrations
      (terminal.from (right.obj X)) := by
    letI : ModelCategory Space := OrdinarySpaceReedyInjective.reedyModel
    letI : CategoryWithFibrations Space :=
      OrdinarySpaceReedyInjective.reedyModel.categoryWithFibrations
    letI : IsFibrant (right.obj X) := OrdinaryJTCurriedAdjunction.right_obj_reedyFibrant X
    exact mem_fibrations _
  rw [isFibrant_iff, fibration_iff]
  change OrdinarySpaceReedyInjective.injectiveModel.categoryWithFibrations.fibrations _
  rw [← OrdinarySpaceReedyInjective.fibrations_eq]
  exact hp

/-- The actual strict ordinary CSS mapping object is the original tensor-frame Hom. -/
def mappingIso (K X : SSet.{0}) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj K) (right.obj X) ≅
      OrdinaryJTMappingFrameWeak.mapping X K :=
  OrdinaryDiscreteMapping.mappingIso K (right.obj X) ≪≫
    OrdinaryJTHorizontalMapping.mappingIso K X

/-- The mapping comparison respects the actual precomposition by every horizontal map. -/
theorem mappingIso_natural {K L : SSet.{0}} (u : K ⟶ L) (X : SSet.{0}) :
    diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map u) (right.obj X) ≫
        (mappingIso K X).hom =
      (mappingIso L X).hom ≫ OrdinaryJTMappingFrameWeak.restriction X u := by
  dsimp only [mappingIso, Iso.trans_hom]
  rw [← Category.assoc, OrdinaryDiscreteMapping.mappingIso_natural,
    Category.assoc, OrdinaryJTHorizontalMapping.mappingIso_natural_source,
    ← Category.assoc]

/-- The original strict test and the actual tensor-frame restriction are isomorphic arrows. -/
def restrictionArrowIso {K L : SSet.{0}} (u : K ⟶ L) (X : SSet.{0}) :
    Arrow.mk (diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map u) (right.obj X)) ≅
      Arrow.mk (OrdinaryJTMappingFrameWeak.restriction X u) :=
  Arrow.isoMk (mappingIso L X) (mappingIso K X) (mappingIso_natural u X).symm

/-- Every original Joyal weak horizontal map gives a weak strict test into the right nerve. -/
theorem mappingPrecomp_weak {K L : SSet.{0}} (u : K ⟶ L)
    (hu : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences u)
    (X : SSet.{0}) [X.Quasicategory] :
    weakEquivalences SSet.{0}
      (diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map u) (right.obj X)) := by
  have h : weakEquivalences SSet.{0} (OrdinaryJTMappingFrameWeak.restriction X u) :=
    (weakEquivalence_iff _).mp
      ((DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
        (OrdinaryJTMappingFrameWeak.restriction_weak X u hu))
  exact ((weakEquivalences SSet.{0}).arrow_mk_iso_iff (restrictionArrowIso u X)).mpr h

/-- The original right nerve passes exactly the ordinary spine and walking tests. -/
theorem right_obj_completeSegal (X : SSet.{0}) [X.Quasicategory] :
    OrdinaryCSSConditions.completeSegalCondition (right.obj X) := by
  constructor
  · intro n _
    exact mappingPrecomp_weak (DaggerNativeStandardSpineInner.spine n).ι
      (DaggerNativeStandardSpineInner.inclusion_categorical_weak n) X
  · exact mappingPrecomp_weak (JTParameterContraction.parameterVertex ⦋1⦌ 0)
      (OrdinaryJTRightNerveCompleteness.parameterVertex_categorical_weak ⦋1⦌ 0) X

/-- The actual right adjoint sends every quasicategory to an ordinary CSS local object. -/
theorem right_obj_localObject (X : SSet.{0}) [X.Quasicategory] :
    Localization.localObject OrdinaryCSSLocalization.localizingFamily (right.obj X) :=
  (OrdinaryCSSConditions.localObject_iff_strict _).mpr
    ⟨right_obj_base_isFibrant X, right_obj_completeSegal X⟩

/-- The same actual right nerve is fibrant in the ordinary CSS localization. -/
theorem right_obj_css_isFibrant (X : SSet.{0}) [X.Quasicategory] :
    @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ (right.obj X) :=
  (OrdinaryCSSLocalization.isFibrant_iff _).mpr (right_obj_localObject X)

#print axioms right_obj_base_isFibrant
#print axioms mappingIso_natural
#print axioms mappingPrecomp_weak
#print axioms right_obj_localObject
#print axioms right_obj_css_isFibrant

end

end DaggerModels.PartII.OrdinaryJTLocality
