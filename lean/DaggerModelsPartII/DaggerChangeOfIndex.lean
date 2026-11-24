import DaggerModelsPartII.DaggerSimplexEnrichment
import DaggerModelsPartII.ProjectiveSegalLocality

/-! The Part II change-of-index adjunctions and their derived locality test. -/

set_option autoImplicit false

open CategoryTheory MorphismProperty HomotopicalAlgebra Opposite
open DaggerModelsPartII.DaggerSimplexIndex
open scoped SSet.modelCategoryQuillen

universe v

namespace DaggerModels.PartII

noncomputable section

open SegalLocalizers

/-- Simplicial presheaves on the free dagger simplex index. -/
abbrev DaggerSpace := DaggerSimplexᵒᵖ ⥤ SSet.{v}

/-- Restriction (u^*) along the actual reversal-to-dagger index functor. -/
abbrev uRestriction : DaggerSpace.{v} ⥤ ReverseDaggerSpace.{v} := restrictIndex.{0, v} u

/-- Left Kan extension (u_!). -/
abbrev uLeftExtension : ReverseDaggerSpace.{v} ⥤ DaggerSpace.{v} := extendIndexLeft.{0, v} u

/-- Right Kan extension (u_*). -/
abbrev uRightExtension : ReverseDaggerSpace.{v} ⥤ DaggerSpace.{v} := extendIndexRight.{0, v} u

/-- The left half of the change-of-index adjoint triple in `h1.lem.adjoints`. -/
def uLeftAdjunction : uLeftExtension.{v} ⊣ uRestriction.{v} := extendIndexLeftAdjunction.{0, v} u

/-- The right half of the change-of-index adjoint triple in `h1.lem.adjoints`. -/
def uRightAdjunction : uRestriction.{v} ⊣ uRightExtension.{v} := extendIndexRightAdjunction.{0, v} u

/-- Restriction along (u) preserves and reflects all levelwise notions. -/
theorem uRestriction_levelwise_iff (P : MorphismProperty SSet.{v})
    {X Y : DaggerSpace.{v}} (f : X ⟶ Y) :
    P.functorCategory ReverseSimplexᵒᵖ (uRestriction.{v}.map f) ↔
      P.functorCategory DaggerSimplexᵒᵖ f :=
  restrictIndex_levelwise_iff.{0, v} u u_obj_bijective.2 P f

/-- Left extension sends reversal representables to the corresponding free
dagger simplex representables, naturally in the index. -/
def uLeftExtension_simplicialYoneda :
    simplicialYoneda.{0, v} ReverseSimplex ⋙ uLeftExtension.{v} ≅
      u ⋙ simplicialYoneda.{0, v} DaggerSimplex :=
  extendIndexLeft_simplicialYoneda.{0, v} u

/-- At a representable, the unit includes the reversal operators into the
full set of dagger functors. -/
theorem uUnit_representable_mono (n : ReverseSimplex) :
    Mono (uLeftAdjunction.{v}.unit.app ((simplicialYoneda.{0, v} ReverseSimplex).obj n)) :=
  extendIndexLeft_unit_simplicialYoneda_mono.{0, v} u n

local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

local instance : ModelCategory DaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory DaggerSimplexᵒᵖ

/-- The change-of-index Quillen adjunction before localization. -/
theorem uLeftAdjunction_projective_isQuillen : uLeftAdjunction.{0}.IsQuillenAdjunction :=
  projectiveIndexAdjunction_isQuillen u

/-- Derived locality at the left Kan images of the resolved Segal family is
equivalent to derived reversal Segal locality after restriction. -/
theorem uProjectiveLocality_iff (W : DaggerSpace.{0}) [IsFibrant W] :
    indexProjectiveSegalLocalizingFamily u ≤ homotopyMappingWeakEquivalences W ↔
      segalLocalizingFamily ≤ homotopyMappingWeakEquivalences (uRestriction.{0}.obj W) :=
  indexProjectiveSegalLocalizingFamily_iff u W

/-- The projectively fibrant local objects for the image family are exactly
the levelwise fibrant diagrams with derived reversal Segal-local restriction. -/
theorem uProjectiveLocalObjects_iff (W : DaggerSpace.{0}) :
    (IsFibrant W ∧ indexProjectiveSegalLocalizingFamily u ≤ homotopyMappingWeakEquivalences W) ↔
      (∀ d, IsFibrant (W.obj d)) ∧
        segalLocalizingFamily ≤ homotopyMappingWeakEquivalences (uRestriction.{0}.obj W) := by
  constructor
  · rintro ⟨hW, h⟩
    letI := hW
    exact ⟨(ProjectiveKanDiagram.model_isFibrant_iff _ W).mp hW,
      (uProjectiveLocality_iff W).mp h⟩
  · rintro ⟨hW, h⟩
    letI := (ProjectiveKanDiagram.model_isFibrant_iff _ W).mpr hW
    exact ⟨inferInstance, (uProjectiveLocality_iff W).mpr h⟩

/-- Restriction reflects local equivalences between projectively fibrant local objects. -/
theorem uRestriction_reflectsLocalEquivalences {X Y : DaggerSpace.{0}} (f : X ⟶ Y)
    (hX : Localization.localObject (indexProjectiveSegalLocalizingFamily u) X)
    (hY : Localization.localObject (indexProjectiveSegalLocalizingFamily u) Y)
    (hf : Localization.localEquivalences segalLocalizingFamily (uRestriction.{0}.map f)) :
    Localization.localEquivalences (indexProjectiveSegalLocalizingFamily u) f := by
  letI := hX.1
  letI := hY.1
  have hRX := (indexProjectiveLocalObject_iff u X).mp hX
  have hRY := (indexProjectiveLocalObject_iff u Y).mp hY
  have hR := (Localization.localEquivalence_iff_weak_of_local
    segalLocalizingFamily (uRestriction.{0}.map f) hRX hRY).mp hf
  have hw : weakEquivalences DaggerSpace.{0} f :=
    (uRestriction_levelwise_iff (weakEquivalences SSet.{0}) f).mp hR
  exact Localization.weakEquivalences_le_localEquivalences _ f hw

end

end DaggerModels.PartII
