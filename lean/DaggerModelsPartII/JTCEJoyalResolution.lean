import ActualDCHRightInducedAndMainTheoremD
import DaggerModelsPartII.JTXiRelativeReedyFrame
import DaggerModelsPartII.StrictFrameMappingTargetWeak
import DaggerModelsPartII.EndpointMappingFiber
import Mathlib.CategoryTheory.Yoneda

/-!
# The literal CE diagram in the original ordinary Joyal undercategory

The latching cofibrations use the already proved monomorphisms of the actual
JT parameter and the reduced-cylinder functor. The module proves the
part of the manuscript's CE resolution needed for target weak invariance.
Weakness of the CE augmentation is a separate proposition and is not used.
The target weak equivalence is measured in the Kan model, while the input
weak equivalence is measured in the original ordinary Joyal model.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
  DaggerModels

namespace DaggerModels.PartII.JTCEJoyalResolution

open JTXiEndpointCollapse GroupoidSimplex JTParameterLatchingMono

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel

private def ordinaryUnderModel : ModelCategory (Under boundary) := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  exact JTEndpointCobase.underModel boundary

private local instance : ModelCategory (Under boundary) := ordinaryUnderModel
private local instance : ModelCategory (Under boundary)ᵒᵖ := inferInstance

private def ordinaryParameterReedyModel :
    ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
  exact simplicialReedyModelCategory SSet.{0}ᵒᵖ

private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
  ordinaryParameterReedyModel
private local instance : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ (Under boundary)ᵒᵖ) :=
  simplicialReedyModelCategory (Under boundary)ᵒᵖ

private def j : boundary ⟶ interval := (SSet.boundary 1).ι
private local instance : Mono j := by
  change Mono (SSet.boundary 1).ι
  infer_instance

private def R : SSet.{0} ⥤ Under boundary := ReducedCylinder.functor j

private local instance : PreservesColimitsOfSize.{0, 0} R := by
  dsimp only [R]
  infer_instance

private local instance : PreservesLimitsOfSize.{0, 0} R.op :=
  preservesLimitsOfSize_op R

/-- The actual completed-simplex parameter is Reedy cofibrant under the
original Joyal model, because its latching maps are literal monomorphisms. -/
private theorem parameter_op_isFibrant : IsFibrant parameter.op := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  apply ((fibrations SSet.{0}ᵒᵖ).cancel_right_of_respectsIso
    ((matchingComparison n).app parameter.op)
    (JTXiOrdinaryLatching.parameterMatchingIso n).hom).mp
  rw [JTXiOrdinaryLatching.parameterMatchingIso_comp, fibrations_op]
  change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
    (faceLatchingMap n)
  -- The exact model cofibrations are the native monomorphisms.
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact faceLatchingMap_mono n

/-- The reduced cylinder preserves original Joyal cofibrations: both are
exactly monomorphisms on their underlying simplicial sets. -/
private theorem R_op_preservesFibrations {X Y : SSet.{0}ᵒᵖ}
    (f : X ⟶ Y) (hf : fibrations SSet.{0}ᵒᵖ f) :
    fibrations (Under boundary)ᵒᵖ (R.op.map f) := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
  rw [fibrations_op] at hf ⊢
  change cofibrations SSet.{0} f.unop at hf
  change cofibrations SSet.{0} ((R.map f.unop).right)
  have hm : Mono f.unop := by
    change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
      f.unop at hf
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof] at hf
    exact hf
  letI : Mono f.unop := hm
  have hR : Mono ((R.map f.unop).right) := ReducedCylinder.map_mono j f.unop
  change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
    ((R.map f.unop).right)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact hR

private theorem reducedParameter_op_isFibrant :
    IsFibrant (parameter ⋙ R).op := by
  letI : IsFibrant parameter.op := parameter_op_isFibrant
  change IsFibrant (parameter.op ⋙ R.op)
  exact reedyFibrant_comp parameter.op R.op
    (fun f hf ↦ R_op_preservesFibrations f hf)

private def H : (SSet.{0} ⥤ SSet.{0}) ⥤ (SimplexCategory ⥤ SSet.{0}) :=
  (Functor.whiskeringLeft SimplexCategory SSet.{0} SSet.{0}).obj parameter

private local instance : PreservesColimitsOfSize.{0, 0} H := by
  dsimp only [H]
  infer_instance

private def ceValueIso : parameter ⋙ ReducedCylinder.value j ≅ CE := by
  change H.obj (pushout (ReducedCylinder.tensorInclusion j)
      (ReducedCylinder.tensorProjection boundary)) ≅
    pushout (H.map (ReducedCylinder.tensorInclusion j))
      (H.map (ReducedCylinder.tensorProjection boundary))
  exact (PreservesPushout.iso H (ReducedCylinder.tensorInclusion j)
    (ReducedCylinder.tensorProjection boundary)).symm

private theorem ceValueIso_boundary :
    Functor.whiskerLeft parameter (ReducedCylinder.boundary j) ≫
        ceValueIso.hom = CE_boundary := by
  change H.map (pushout.inr (ReducedCylinder.tensorInclusion j)
      (ReducedCylinder.tensorProjection boundary)) ≫
        (PreservesPushout.iso H (ReducedCylinder.tensorInclusion j)
          (ReducedCylinder.tensorProjection boundary)).inv =
    pushout.inr (H.map (ReducedCylinder.tensorInclusion j))
      (H.map (ReducedCylinder.tensorProjection boundary))
  exact PreservesPushout.inr_iso_inv H
    (ReducedCylinder.tensorInclusion j)
    (ReducedCylinder.tensorProjection boundary)

private def ceUnderIso : parameter ⋙ R ≅ Under.lift CE CE_boundary :=
  NatIso.ofComponents
    (fun k ↦ Under.isoMk (ceValueIso.app k)
      (NatTrans.congr_app ceValueIso_boundary k))
    (by
      intro k l f
      apply Under.UnderMorphism.ext
      exact ceValueIso.hom.naturality f)

/-- The actual CE diagram with its ordered boundary is Reedy cofibrant in
the undercategory for the original ordinary Joyal model. -/
theorem ceUnder_op_isFibrant : IsFibrant (Under.lift CE CE_boundary).op := by
  letI : IsFibrant (parameter ⋙ R).op := reducedParameter_op_isFibrant
  let e := NatIso.op ceUnderIso
  haveI : Fibration e.hom := inferInstance
  exact isFibrant_of_fibration e.hom

/-- The literal fixed-boundary CE Hom simplicial set, covariant in the
ordinary simplicial set under the ordered boundary. -/
def mapE : Under boundary ⥤ SSet.{0} :=
  StrictFrameMappingTargetWeak.mapping (Under.lift CE CE_boundary).op

/-- The native coyoneda presentation is the literal Hom simplicial set from
the original CE diagram under its ordered boundary. -/
def mapE_plainIso (X : Under boundary) :
    mapE.obj X ≅
      EndpointMappingFiber.mapping (Z := X) (Under.lift CE CE_boundary) :=
  Functor.isoWhiskerLeft (Under.lift CE CE_boundary).op
    (Coyoneda.objOpOp X)

/-- The actual CE Hom simplicial set preserves original Joyal weak maps
between fibrant under-boundary targets. No CE augmentation hypothesis enters. -/
theorem mapE_map_weak {X Y : Under boundary} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y)
    (hf : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences f.right) :
    DaggerSSetGluing.GW (mapE.map f) := by
  letI : IsFibrant (Under.lift CE CE_boundary).op := ceUnder_op_isFibrant
  have hfUnder : weakEquivalences (Under boundary) f := by
    change (JTEndpointCobase.underModel boundary).categoryWithWeakEquivalences.weakEquivalences f
    rw [JTEndpointCobase.underModel_weakEquivalences]
    simp only [MorphismProperty.under_iff]
    change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithWeakEquivalences.weakEquivalences
      f.right
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
    exact hf
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  have h : weakEquivalences SSet.{0} (mapE.map f) :=
    StrictFrameMappingTargetWeak.mapping_map_weak
      (Under.lift CE CE_boundary).op f hfUnder
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    ((weakEquivalence_iff _).2 h)

end

end DaggerModels.PartII.JTCEJoyalResolution
