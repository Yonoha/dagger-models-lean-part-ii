import OrdinarySegalHorizontalCotensor
import OrdinaryJTOrdinaryInputReedy
import OrdinarySpaceReedyInjective
import DaggerModelsPartII.StandardSimplexFrame
import DaggerModelsPartII.ReedyFibrantDiagrams
import DaggerModelsPartII.DiagramMappingPrecompFibration
import NativeIhomRelativeSectionsWeak

/-!
# Injective Kan fibrancy of horizontal cotensors

The standard-simplex opposite is Reedy fibrant over the native Kan model.
Cartesian tensor by an arbitrary horizontal parameter preserves colimits
and monomorphisms, hence its opposite preserves limits and fibrations.
The strict discrete-source mapping functor into an injective fibrant space
has the same two preservation properties. Two coefficient changes and the
checked Reedy-injective identification give fibrancy of the literal
horizontal cotensor, without a Segal or completeness assumption.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
  MorphismProperty MonoidalCategory DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorFibrant

noncomputable section

private abbrev Space := OrdinaryCSSLocalization.Space
private abbrev discrete := OrdinaryCSSLocalization.discrete
private abbrev mapping (W : Space) := OrdinaryJTOrdinaryInputReedy.mappingFunctor W

private local instance : ModelCategory SSet.{0}ᵒᵖ := inferInstance
private local instance : CategoryWithFibrations SSet.{0}ᵒᵖ :=
  (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithFibrations
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{0}ᵒᵖ

private local instance (K : SSet.{0}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft K) :=
  (ihom.adjunction K).leftAdjoint_preservesColimits

private local instance (K : SSet.{0}) :
    PreservesLimitsOfSize.{0, 0} (tensorLeft K).op :=
  preservesLimitsOfSize_op (tensorLeft K)

private theorem tensorLeft_op_map_fibration (K : SSet.{0})
    {A B : SSet.{0}ᵒᵖ} (f : A ⟶ B)
    (hf : fibrations SSet.{0}ᵒᵖ f) :
    fibrations SSet.{0}ᵒᵖ ((tensorLeft K).op.map f) := by
  rw [fibrations_op] at hf ⊢
  haveI : Mono f.unop := by
    change cofibrations SSet.{0} f.unop at hf
    rw [SSet.modelCategoryQuillen.cofibrations_eq] at hf
    exact hf
  haveI : Mono (K ◁ f.unop) :=
    DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono K f.unop
  change cofibrations SSet.{0} (K ◁ f.unop)
  rw [SSet.modelCategoryQuillen.cofibrations_eq]
  change Mono (K ◁ f.unop)
  infer_instance

private local instance : PreservesColimitsOfSize.{0, 0} discrete := by
  letI : PreservesColimitsOfSize.{0, 0}
      (SimplicialObject.const (Type 0)) :=
    CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)
  change PreservesColimitsOfSize.{0, 0}
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ
      (Type 0) SSet.{0}).obj (SimplicialObject.const (Type 0)))
  infer_instance

private local instance : PreservesLimitsOfSize.{0, 0} discrete.op :=
  preservesLimitsOfSize_op discrete

private local instance (W : Space) :
    PreservesLimitsOfSize.{0, 0} (diagramMappingSource W) :=
  ⟨fun {J} _ ↦ by
    letI : HasColimitsOfShape Jᵒᵖ SSet.{0} := inferInstance
    exact diagramMappingSource_preservesLimitsOfShape J W⟩

private local instance (W : Space) :
    PreservesLimitsOfSize.{0, 0} (mapping W) := by
  dsimp [mapping, OrdinaryJTOrdinaryInputReedy.mappingFunctor]
  infer_instance

private theorem mapping_map_fibration (W : Space)
    (hW : @IsFibrant Space _
      OrdinarySpaceReedyInjective.injectiveModel.categoryWithFibrations _ W)
    {A B : SSet.{0}ᵒᵖ} (f : A ⟶ B)
    (hf : fibrations SSet.{0}ᵒᵖ f) :
    fibrations SSet.{0} ((mapping W).map f) := by
  rw [fibrations_op] at hf
  haveI : Mono f.unop := by
    change cofibrations SSet.{0} f.unop at hf
    rw [SSet.modelCategoryQuillen.cofibrations_eq] at hf
    exact hf
  haveI : Mono (discrete.map f.unop) :=
    OrdinaryCSSLocalization.discrete_map_mono f.unop
  letI : ModelCategory Space := OrdinarySpaceReedyInjective.injectiveModel
  letI : IsFibrant W := hW
  change fibrations SSet.{0}
    (diagramMappingPrecomp (discrete.map f.unop) W)
  exact (fibration_iff _).mp
    (InjectiveKanDiagram.diagramMappingPrecomp_isFibration
      SimplexCategoryᵒᵖ (discrete.map f.unop) W)

/-- Every literal horizontal cotensor of an injective Kan fibrant
ordinary simplicial space is injective Kan fibrant. -/
theorem cotensor_injectiveFibrant (K : SSet.{0}) (W : Space)
    (hW : @IsFibrant Space _
      OrdinarySpaceReedyInjective.injectiveModel.categoryWithFibrations _ W) :
    @IsFibrant Space _
      OrdinarySpaceReedyInjective.injectiveModel.categoryWithFibrations _
      (OrdinarySegalHorizontalCotensor.cotensor K W) := by
  have h₁ : IsFibrant
      (SSet.stdSimplex.{0}.op ⋙ (tensorLeft K).op) := by
    letI : IsFibrant SSet.stdSimplex.{0}.op :=
      standardSimplex_op_reedyFibrant
    exact reedyFibrant_comp SSet.stdSimplex.{0}.op
      (tensorLeft K).op (tensorLeft_op_map_fibration K)
  have hR : @IsFibrant Space _
      OrdinarySpaceReedyInjective.reedyModel.categoryWithFibrations _
      (OrdinarySegalHorizontalCotensor.cotensor K W) := by
    letI : ModelCategory Space := OrdinarySpaceReedyInjective.reedyModel
    letI : IsFibrant
        (SSet.stdSimplex.{0}.op ⋙ (tensorLeft K).op) := h₁
    change IsFibrant
      ((SSet.stdSimplex.{0}.op ⋙ (tensorLeft K).op) ⋙ mapping W)
    exact reedyFibrant_comp
      (SSet.stdSimplex.{0}.op ⋙ (tensorLeft K).op)
      (mapping W) (mapping_map_fibration W hW)
  have hf :
      OrdinarySpaceReedyInjective.reedyModel.categoryWithFibrations.fibrations
        (terminal.from (OrdinarySegalHorizontalCotensor.cotensor K W)) := by
    letI : ModelCategory Space := OrdinarySpaceReedyInjective.reedyModel
    exact (fibration_iff _).mp hR
  have hi :
      OrdinarySpaceReedyInjective.injectiveModel.categoryWithFibrations.fibrations
        (terminal.from (OrdinarySegalHorizontalCotensor.cotensor K W)) := by
    rw [← OrdinarySpaceReedyInjective.fibrations_eq]
    exact hf
  letI : ModelCategory Space := OrdinarySpaceReedyInjective.injectiveModel
  exact (fibration_iff _).mpr hi

#print axioms cotensor_injectiveFibrant

end

end DaggerModels.PartII.OrdinarySegalCotensorFibrant
