import DaggerModelsPartII.ResolvedRestrictionLocality
import DaggerModelsPartII.ActualInjectiveSegalLocalization
import DaggerModelsPartII.LocalizedQuillenDescent
import DaggerModelsPartII.CosimplicialQuillenComparison
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Restriction as a left Quillen functor after actual injective localization

The actual precomposition functor is left adjoint to right Kan extension.
The local weak equivalence of the restricted actual image generators makes
this adjunction left Quillen after injective Segal localization.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels
open DaggerModels.PartII.DaggerSimplexPartIIndex
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.RestrictionInjectiveQuillen

open SegalLocalizers ActualIndexProjectiveModel

noncomputable section

private theorem actualRightAdjunction_baseInjective_isQuillen :
    @Adjunction.IsQuillenAdjunction ActualSpace ReverseDaggerSpace.{0} _ _
      (InjectiveKanDiagram.modelCategory ActualDaggerSimplexᵒᵖ)
      (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ)
      actualRestriction.{0} actualRightExtension.{0}
      actualRightAdjunction.{0} := by
  letI : ModelCategory ActualSpace :=
    InjectiveKanDiagram.modelCategory ActualDaggerSimplexᵒᵖ
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have preserveMono {X Y : ActualSpace} (f : X ⟶ Y) [Mono f] :
      Mono (actualRestriction.{0}.map f) := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro c
    exact (NatTrans.mono_iff_mono_app f).mp inferInstance (actualU.op.obj c)
  have hcof : actualRestriction.{0}.PreservesCofibrations := by
    apply actualRestriction.{0}.preservesCofibrations_iff.mpr
    intro X Y f hf
    rw [InjectiveKanDiagram.model_cofibrations] at hf ⊢
    rw [monomorphisms.iff] at hf
    change (monomorphisms _) (actualRestriction.{0}.map f)
    rw [monomorphisms.iff]
    haveI : Mono f := hf
    exact preserveMono f
  have htriv : actualRestriction.{0}.PreservesTrivialCofibrations := by
    apply actualRestriction.{0}.preservesTrivialCofibrations_iff.mpr
    intro X Y f hf
    change cofibrations ActualSpace f ∧ weakEquivalences ActualSpace f at hf
    change cofibrations ReverseDaggerSpace.{0} (actualRestriction.{0}.map f) ∧
      weakEquivalences ReverseDaggerSpace.{0} (actualRestriction.{0}.map f)
    rw [InjectiveKanDiagram.model_cofibrations,
      InjectiveKanDiagram.model_weakEquivalences] at hf ⊢
    rw [monomorphisms.iff] at hf
    rw [monomorphisms.iff]
    haveI : Mono f := hf.1
    exact ⟨preserveMono f,
      (actualRestriction_levelwise_iff (weakEquivalences SSet.{0}) f).mpr hf.2⟩
  have hfib : actualRightExtension.{0}.PreservesFibrations :=
    (actualRightAdjunction.{0}).preservesTrivialCofibrations_iff_preservesFibrations.mp
      htriv
  letI := hcof
  letI := hfib
  exact ⟨⟩

private theorem actualRightExtension_localObject (Z : ReverseDaggerSpace.{0})
    (hZ : @Localization.localObject ReverseDaggerSpace.{0} _
      (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ) _ _
      segalLocalizingFamily Z) :
    @Localization.localObject ActualSpace _
      (InjectiveKanDiagram.modelCategory ActualDaggerSimplexᵒᵖ) _ _
      (functorialImageSRev actualU) (actualRightExtension.{0}.obj Z) := by
  letI : ModelCategory ActualSpace :=
    InjectiveKanDiagram.modelCategory ActualDaggerSimplexᵒᵖ
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : actualRightAdjunction.{0}.IsQuillenAdjunction :=
    actualRightAdjunction_baseInjective_isQuillen
  letI : IsFibrant Z := hZ.1
  letI : actualRightExtension.{0}.PreservesFibrations :=
    Adjunction.IsQuillenAdjunction.preservesFibrations actualRightAdjunction.{0}
  letI : PreservesLimitsOfSize.{0, 0} actualRightExtension.{0} :=
    actualRightAdjunction.{0}.rightAdjoint_preservesLimits
  haveI hSZ : IsFibrant (actualRightExtension.{0}.obj Z) := by
    exact (isFibrant_iff_of_isTerminal
      (actualRightExtension.{0}.map (terminal.from Z))
      (terminalIsTerminal.isTerminalObj actualRightExtension.{0})).mpr inferInstance
  refine ⟨hSZ, ?_⟩
  intro A B f hf
  obtain ⟨i⟩ := hf
  letI : IsCofibrant (actualImageLocalizer i).left :=
    InjectiveKanDiagram.model_isCofibrant ActualDaggerSimplexᵒᵖ _
  letI : IsCofibrant (actualImageLocalizer i).right :=
    InjectiveKanDiagram.model_isCofibrant ActualDaggerSimplexᵒᵖ _
  letI : IsCofibrant ((𝟭 ActualSpace).obj (actualImageLocalizer i).left) := by
    change IsCofibrant (actualImageLocalizer i).left
    infer_instance
  letI : IsCofibrant ((𝟭 ActualSpace).obj (actualImageLocalizer i).right) := by
    change IsCofibrant (actualImageLocalizer i).right
    infer_instance
  have hR : Localization.localEquivalences segalLocalizingFamily
      ((actualRestriction.{0}).map (actualImageLocalizer i).hom) := by
    have h := ResolvedRestrictionLocality.actualRestriction_imageLocalizer_localWeak i
    rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).2] at h
    exact h
  have htest : homotopyMappingWeakEquivalences Z
      ((actualRestriction.{0}).map (actualImageLocalizer i).hom) := hR Z hZ
  exact (homotopyMappingWeakEquivalences_leftQuillen_iff
    actualRightAdjunction.{0} (actualImageLocalizer i).hom Z).mp htest

/-- The exact restriction/right-Kan adjunction is Quillen after both
injective Segal localizations. -/
theorem actualRightAdjunction_localizedInjective_isQuillen :
    @Adjunction.IsQuillenAdjunction ActualSpace ReverseDaggerSpace.{0} _ _
      actualInjectiveSegalModel injectiveSegalModel
      actualRestriction.{0} actualRightExtension.{0}
      actualRightAdjunction.{0} := by
  have hA := InjectiveKanDiagram.localized_exactClasses ActualDaggerSimplexᵒᵖ
    LocalizerIndex actualImageLocalizer actualImageLocalizer_mono
  have hR := InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  exact Localization.localizedQuillen_of_rightLocal
    (InjectiveKanDiagram.modelCategory ActualDaggerSimplexᵒᵖ)
    (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ)
    (functorialImageSRev actualU) segalLocalizingFamily
    actualInjectiveSegalModel injectiveSegalModel
    hA.1 hA.2 hR.1 hR.2
    actualRestriction.{0} actualRightExtension.{0} actualRightAdjunction.{0}
    actualRightAdjunction_baseInjective_isQuillen actualRightExtension_localObject

private theorem actualInjective_allCofibrant (X : ActualSpace) :
    @IsCofibrant ActualSpace _
      actualInjectiveSegalModel.categoryWithCofibrations _ X := by
  have hbase : @IsCofibrant ActualSpace _
      (InjectiveKanDiagram.modelCategory ActualDaggerSimplexᵒᵖ).categoryWithCofibrations
        _ X := by
    letI : ModelCategory ActualSpace :=
      InjectiveKanDiagram.modelCategory ActualDaggerSimplexᵒᵖ
    exact InjectiveKanDiagram.model_isCofibrant ActualDaggerSimplexᵒᵖ X
  have hcof : (InjectiveKanDiagram.modelCategory
      ActualDaggerSimplexᵒᵖ).categoryWithCofibrations.cofibrations
        (initial.to X) := by
    letI : CategoryWithCofibrations ActualSpace :=
      (InjectiveKanDiagram.modelCategory
        ActualDaggerSimplexᵒᵖ).categoryWithCofibrations
    exact (cofibration_iff (initial.to X)).mp hbase
  have hloc : actualInjectiveSegalModel.categoryWithCofibrations.cofibrations
      (initial.to X) := by
    rw [(InjectiveKanDiagram.localized_exactClasses ActualDaggerSimplexᵒᵖ
      LocalizerIndex actualImageLocalizer actualImageLocalizer_mono).1]
    exact hcof
  letI : CategoryWithCofibrations ActualSpace :=
    actualInjectiveSegalModel.categoryWithCofibrations
  exact (cofibration_iff (initial.to X)).mpr hloc

/-- Restriction preserves every weak equivalence of the actual injective
Segal localization. -/
theorem actualRestriction_preservesLocalizedInjectiveWeak
    {X Y : ActualSpace} (f : X ⟶ Y)
    (hf : actualInjectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences f) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (actualRestriction.{0}.map f) := by
  letI : ModelCategory ActualSpace := actualInjectiveSegalModel
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  letI : actualRightAdjunction.{0}.IsQuillenAdjunction :=
    actualRightAdjunction_localizedInjective_isQuillen
  letI : IsCofibrant X := actualInjective_allCofibrant X
  letI : IsCofibrant Y := actualInjective_allCofibrant Y
  letI : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  let d : CofibrantBrownFactorization f := Classical.choice inferInstance
  letI : actualRestriction.{0}.PreservesTrivialCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
      actualRightAdjunction.{0}
  haveI hi : WeakEquivalence (actualRestriction.{0}.map d.i) := inferInstance
  haveI hs : WeakEquivalence (actualRestriction.{0}.map d.s) := inferInstance
  have hsection : actualRestriction.{0}.map d.s ≫
      actualRestriction.{0}.map d.p = 𝟙 _ := by
    rw [← Functor.map_comp, d.s_p]
    exact actualRestriction.{0}.map_id Y
  haveI hp : WeakEquivalence (actualRestriction.{0}.map d.p) :=
    weakEquivalence_of_precomp_of_fac hsection
  haveI hcomp : WeakEquivalence
      (actualRestriction.{0}.map d.i ≫ actualRestriction.{0}.map d.p) := inferInstance
  have hresult : WeakEquivalence (actualRestriction.{0}.map f) := by
    rwa [← Functor.map_comp, d.fac] at hcomp
  exact (weakEquivalence_iff _).mp hresult

/-- The projective and injective actual localizations have the same weak
class, so restriction preserves every projective-localized weak equivalence. -/
theorem actualRestriction_preservesLocalizedProjectiveWeak
    {X Y : ActualSpace} (f : X ⟶ Y)
    (hf : actualSegalModel.categoryWithWeakEquivalences.weakEquivalences f) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (actualRestriction.{0}.map f) := by
  apply actualRestriction_preservesLocalizedInjectiveWeak f
  rw [← actualSegalModels_weakEquivalences_eq]
  exact hf

end

end DaggerModels.PartII.RestrictionInjectiveQuillen
