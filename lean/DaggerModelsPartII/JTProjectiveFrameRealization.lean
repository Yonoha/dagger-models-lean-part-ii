import DaggerModelsPartII.JTSegalFrameLocality
import DaggerModelsPartII.JTStrictificationMaps
import DaggerModelsPartII.JTStrictTransport
import DaggerModelsPartII.WeakFunctorBrown

/-! The literal projectively resolved frame realization and its comparison on
constant-vertex diagrams. -/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.JTProjectiveFrameRealization

open SegalLocalizers JTFrameAdjunction JTStrictificationMaps ConstantVertexAdjunction
open OrdinaryRigidification.DaggerRigidification

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} := projectiveSegalModel
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- Resolve the diagram by the original projective boundary factorization and
then apply the original frame realization. -/
def projectiveFrameRealization : ReverseDaggerSpace.{0} ⥤ DaggerSimplicialCat.{0, 0} :=
  Qproj ⋙ frameRealization

private theorem local_cof_eq :
    projectiveSegalModel.categoryWithCofibrations.cofibrations =
      (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations :=
  (ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).1

private theorem projective_weak_is_local_weak
    {W Z : ReverseDaggerSpace.{0}} (f : W ⟶ Z)
    (hf : (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithWeakEquivalences.weakEquivalences f) :
    weakEquivalences ReverseDaggerSpace.{0} f := by
  change projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences f
  rw [(ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).2]
  letI : ModelCategory ReverseDaggerSpace.{0} := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  exact Localization.weakEquivalences_le_localEquivalences _ f hf

private theorem projectiveResolution_cofibrant (W : ReverseDaggerSpace.{0}) :
    IsCofibrant (Qproj.obj W) := by
  rw [isCofibrant_iff, cofibration_iff]
  change projectiveSegalModel.categoryWithCofibrations.cofibrations _
  rw [local_cof_eq]
  letI : ModelCategory ReverseDaggerSpace.{0} := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI := Qproj_cofibrant W
  exact mem_cofibrations _

/-- The functor on resolved diagrams sends all projective Segal weak
equivalences to original dagger Bergner weak equivalences. -/
theorem projectiveFrameRealization_map_weak {W Z : ReverseDaggerSpace.{0}} (f : W ⟶ Z)
    (hf : weakEquivalences ReverseDaggerSpace.{0} f) :
    weakEquivalences DaggerSimplicialCat.{0, 0} (projectiveFrameRealization.map f) := by
  let P := weakEquivalences ReverseDaggerSpace.{0}
  have hw : P (p.app W) := projective_weak_is_local_weak _ (p_trivialFibration W).2
  have hz : P (p.app Z) := projective_weak_is_local_weak _ (p_trivialFibration Z).2
  have hq : P (Qproj.map f) := by
    apply P.of_postcomp _ _ hz
    rw [p.naturality f]
    exact P.comp_mem _ _ hw hf
  letI : IsCofibrant (Qproj.obj W) := projectiveResolution_cofibrant W
  letI : IsCofibrant (Qproj.obj Z) := projectiveResolution_cofibrant Z
  letI : JTFrameAdjunction.adjunction.IsQuillenAdjunction :=
    JTSegalFrameLocality.localized_isQuillenAdjunction
  letI := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations JTFrameAdjunction.adjunction
  apply WeakFunctorBrown.map_weak_on_cofibrant frameRealization
    (weakEquivalences DaggerSimplicialCat.{0, 0}) _ _ hq
  intro A B i hi
  exact (Functor.PreservesTrivialCofibrations.trivialCofibrations_le frameRealization i hi).2

/-- The actual augmentation followed by the original strict transport. -/
def compareRigidification : delta ⋙ projectiveFrameRealization ⟶ daggerRigidification :=
  (Functor.associator delta Qproj frameRealization).inv ≫
    Functor.whiskerRight (Functor.whiskerLeft delta p) frameRealization ≫
      JTStrictTransport.Theta.hom

/-- The comparison on constant vertices is objectwise dagger Bergner weak. -/
theorem compareRigidification_weak (X : DaggerSSet.{0}) :
    weakEquivalences DaggerSimplicialCat.{0, 0} (compareRigidification.app X) := by
  change weakEquivalences DaggerSimplicialCat.{0, 0}
    (𝟙 _ ≫ (frameRealization.map (p.app (delta.obj X)) ≫ JTStrictTransport.Theta.hom.app X))
  rw [Category.id_comp]
  apply (weakEquivalences DaggerSimplicialCat.{0, 0}).comp_mem
  · letI : ModelCategory ReverseDaggerSpace.{0} := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    letI := Qproj_cofibrant (delta.obj X)
    exact JTCofibrantAugmentationWeak.frameRealization_augmentation_weak X
      (p.app (delta.obj X)) (p_trivialFibration (delta.obj X)).2
  · exact (weakEquivalences DaggerSimplicialCat.{0, 0}).of_isIso _

end

end DaggerModels.PartII.JTProjectiveFrameRealization
