import DaggerModelsPartII.LocalizingDiagramGenerators
import DaggerModelsPartII.AccessibleTerminalReplacement
import DaggerModelsPartII.InjectiveLocalEquivalences
import DaggerModelsPartII.LocalizingBoundaryLocality

/-!
# Accessible local replacement of injective simplicial-set diagrams

Apply the accessible small object argument to the explicit Smith generators
and the boundary boxes of a small monomorphism family.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

noncomputable section

local instance replacementInjectiveModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C
local instance replacementLocallyPresentable : IsLocallyPresentable.{u} (C ⥤ SSet.{u}) :=
  ProjectiveKanDiagram.locallyPresentable C

/-- The accessible local replacement built from the explicit joint family. -/
def localReplacement (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) :
    (C ⥤ SSet.{u}) ⥤ (C ⥤ SSet.{u}) :=
  SmallObjectReplacement.replacement (localizingFibrancyGenerators C I s)

/-- The natural unit of local replacement. -/
def localReplacementUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) :
    𝟭 (C ⥤ SSet.{u}) ⟶ localReplacement C I s :=
  SmallObjectReplacement.unit (localizingFibrancyGenerators C I s)

/-- The replacement is local for the original monomorphism family. -/
theorem localReplacement_isLocal (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom)
    (X : C ⥤ SSet.{u}) :
    Localization.localObject (diagramLocalizingFamily C I s)
      ((localReplacement C I s).obj X) := by
  apply (localizingFibrancyGenerators_rlp_terminal_iff_localObject C I s hs _).mp
  exact SmallObjectReplacement.terminal_mem_rlp (localizingFibrancyGenerators C I s) X

/-- The natural local-replacement unit is an injective cofibration. -/
theorem localReplacementUnit_cofibration (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom)
    (X : C ⥤ SSet.{u}) :
    HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u})
      ((localReplacementUnit C I s).app X) := by
  have h := SmallObjectReplacement.unit_mem_llp (localizingFibrancyGenerators C I s) X
  rw [← llp_eq_of_wfs (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}))
    (HomotopicalAlgebra.trivialFibrations (C ⥤ SSet.{u}))]
  intro A B p hp
  exact h p (fun D E f hf ↦ hasLiftingProperty_of_wfs _ _
    (localizingFibrancyGenerators_le_cofibrations C I s hs f hf) hp)

/-- The explicit local replacement functor preserves sufficiently filtered colimits. -/
theorem localReplacement_accessible (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) :
    Functor.IsAccessible.{u} (localReplacement C I s) :=
  SmallObjectReplacement.replacement_accessible (localizingFibrancyGenerators C I s)

/-- Every boundary box is a local equivalence for the original family. -/
theorem localizingBoundaryBoxes_le_localEquivalences (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom) :
    localizingBoundaryBoxes C I s ≤
      Localization.localEquivalences (diagramLocalizingFamily C I s) := by
  intro A B f hf W hW
  obtain ⟨⟨i, n⟩⟩ := hf
  letI : Mono (s i).hom := hs i
  letI : IsFibrant W := hW.1
  have hi : homotopyMappingWeakEquivalences W (s i).hom := hW.2 _ ⟨i⟩
  exact diagramPushoutProduct_local C (s i).hom (SSet.boundary n).ι W
    (diagramPushoutProduct C (s i).hom (SSet.boundary n).ι) hi

private theorem localReplacementUnit_localEquivalence_of_boxes (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom)
    (hboxes : localizingBoundaryBoxes C I s ≤
      Localization.localEquivalences (diagramLocalizingFamily C I s))
    (X : C ⥤ SSet.{u}) :
    Localization.localEquivalences (diagramLocalizingFamily C I s)
      ((localReplacementUnit C I s).app X) := by
  let S := diagramLocalizingFamily C I s
  let P := HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
    Localization.localEquivalences S
  letI : P.IsStableUnderCobaseChange := localTrivialCofibrations_cobaseChange C S
  letI : IsStableUnderTransfiniteComposition.{u} P :=
    localTrivialCofibrations_transfinite C S
  letI : P.IsStableUnderRetracts := inferInstance
  have hK : localizingFibrancyGenerators C I s ≤ P := by
    refine sup_le ?_ ?_
    · intro A B f hf
      have ht := injectiveSmithJ_le_trivialCofibrations C f hf
      exact ⟨ht.1, Localization.weakEquivalences_le_localEquivalences S f ht.2⟩
    · intro A B f hf
      exact ⟨localizingBoundaryBoxes_le_cofibrations C I s hs f hf, hboxes f hf⟩
  exact (SmallObjectReplacement.unit_mem_of_stable
    (localizingFibrancyGenerators C I s) P hK X).2

private theorem localEquivalences_eq_inverseImage_of_boxes (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom)
    (hboxes : localizingBoundaryBoxes C I s ≤
      Localization.localEquivalences (diagramLocalizingFamily C I s)) :
    Localization.localEquivalences (diagramLocalizingFamily C I s) =
      (HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u})).inverseImage
        (localReplacement C I s) := by
  exact Localization.localEquivalences_eq_inverseImage
    (diagramLocalizingFamily C I s) (localReplacement C I s)
    (localReplacementUnit C I s) (localReplacement_isLocal C I s hs)
    (localReplacementUnit_localEquivalence_of_boxes C I s hs hboxes)

/-- The natural unit of the explicit local replacement is a local equivalence. -/
theorem localReplacementUnit_localEquivalence (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom)
    (X : C ⥤ SSet.{u}) :
    Localization.localEquivalences (diagramLocalizingFamily C I s)
      ((localReplacementUnit C I s).app X) :=
  localReplacementUnit_localEquivalence_of_boxes C I s hs
    (localizingBoundaryBoxes_le_localEquivalences C I s hs) X

/-- Exact local equivalences are the inverse image of original weak equivalences
under the accessible local replacement functor. -/
theorem localEquivalences_eq_inverseImage (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom) :
    Localization.localEquivalences (diagramLocalizingFamily C I s) =
      (HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u})).inverseImage
        (localReplacement C I s) :=
  localEquivalences_eq_inverseImage_of_boxes C I s hs
    (localizingBoundaryBoxes_le_localEquivalences C I s hs)

end

end DaggerModels.PartII.InjectiveKanDiagram
