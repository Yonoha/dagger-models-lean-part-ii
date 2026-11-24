import DaggerModelsPartII.LocalizedInjectiveSimplicial
import DaggerModelsPartII.DiagramMappingPrecompFibration

/-!
# Localized mapping corners

The pushout-product theorem gives a trivial Kan fibration of strict mapping
spaces for a localized trivial cofibration and a localized fibration.
The corner is the actual pullback object of the tensor-mapping adjunction.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

noncomputable section

/-- A localized trivial cofibration induces a trivial Kan mapping corner
against every localized fibration. -/
theorem localized_mappingCorner_trivialFibration
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ k, Mono (s k).hom)
    {A B X Y : C ⥤ SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations i)
    (hwi : (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences i)
    (hp : (localizedModelCategory C I s hs).categoryWithFibrations.fibrations p)
    (corner : (diagramMappingSource C).PullbackObjObj i p) :
    trivialFibrations SSet.{u} corner.π := by
  rw [← cofibrations_rlp]
  intro K L j hj
  let sq := diagramPushoutProduct C i j
  have hbox := localized_pushoutProduct_sm7 C I s hs i j hi hj sq
  have hboxW := hbox.2 (Or.inl hwi)
  have hl : HasLiftingProperty sq.ι p := by
    letI : ModelCategory (C ⥤ SSet.{u}) := localizedModelCategory C I s hs
    haveI : Cofibration sq.ι := (cofibration_iff _).mpr hbox.1
    haveI : WeakEquivalence sq.ι := (weakEquivalence_iff _).mpr hboxW
    haveI : Fibration p := (fibration_iff _).mpr hp
    infer_instance
  exact ((diagramParametrizedAdjunction C).hasLiftingProperty_iff sq corner).mp hl

end

end DaggerModels.PartII.InjectiveKanDiagram
