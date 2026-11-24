import DaggerModelsPartII.InjectiveLocalizationModel
import DaggerModelsPartII.SegalLocalizers
import DaggerModelsPartII.JTParameterContraction
import DaggerModelsPartII.JTParameterVertexKan

/-!
# Ordinary complete-Segal-space localization

The horizontal simplicial-space category is `SimplexCategoryᵒᵖ ⥤ SSet`.
The two literal localizers are the discretized ordinary spine inclusion and
the discretized selected vertex of the groupoid-completed one-simplex.
`InjectiveKanDiagram.localizedModelCategory` supplies the localization;
`localized_exactClasses` and `localized_isFibrant_iff` identify its exact
cofibration, weak-equivalence, and local-fibrancy interfaces. This stage does
not identify the injective and Reedy model structures or assert a JT Quillen
equivalence. No completeness condition is placed on an ordinary input.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerModels.PartII
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCSSLocalization

noncomputable section

/-- Ordinary simplicial spaces, with the first index horizontal. -/
abbrev Space := SimplexCategoryᵒᵖ ⥤ SSet.{0}

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Put a simplicial set in the horizontal index and discretize each value. -/
def discrete : SSet.{0} ⥤ Space :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
    (SimplicialObject.const (Type 0))

/-- Horizontal discretization preserves monomorphisms pointwise. -/
theorem discrete_map_mono {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f] :
    Mono (discrete.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [NatTrans.mono_iff_mono_app]
  intro k
  change Mono (f.app a)
  exact (NatTrans.mono_iff_mono_app _).mp (inferInstance : Mono f) a

/-- The actual ordinary horizontal spine localizer in dimension `n`. -/
def spineMap (n : ℕ) :
    discrete.obj ((DaggerNativeStandardSpineInner.spine n).toSSet) ⟶
      discrete.obj (Δ[n] : SSet.{0}) :=
  discrete.map (DaggerNativeStandardSpineInner.spine n).ι

theorem spineMap_mono (n : ℕ) : Mono (spineMap n) := by
  letI : Mono (DaggerNativeStandardSpineInner.spine n).ι := inferInstance
  exact discrete_map_mono _

/-- The horizontal nerve of the ordinary walking isomorphism. -/
def walkingSpace : Space := discrete.obj (GroupoidSimplex.parameter.obj ⦋1⦌)

/-- The selected-vertex completeness localizer of ordinary CSS. -/
def completenessMap : discrete.obj (Δ[0] : SSet.{0}) ⟶ walkingSpace :=
  discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ 0)

theorem completenessMap_mono : Mono completenessMap := by
  letI : Mono (JTParameterContraction.parameterVertex ⦋1⦌ 0) :=
    JTParameterVertexKan.vertex_mono ⦋1⦌ 0
  exact discrete_map_mono _

/-- All ordinary Segal localizers and the one ordinary completeness localizer. -/
abbrev LocalizerIndex := {n : ℕ // 2 ≤ n} ⊕ Unit

def localizerArrow : LocalizerIndex → Arrow Space := fun i ↦ match i with
  | .inl n => Arrow.mk (spineMap n)
  | .inr _ => Arrow.mk completenessMap

theorem localizerArrow_mono (i : LocalizerIndex) :
    Mono (localizerArrow i).hom := by
  cases i with
  | inl n => exact spineMap_mono n
  | inr _ => exact completenessMap_mono

/-- The exact small family presented by the two kinds of ordinary maps. -/
def localizingFamily : MorphismProperty Space :=
  InjectiveKanDiagram.diagramLocalizingFamily SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow

/-- The ordinary CSS localization of the injective Kan diagram model. -/
def model : ModelCategory Space :=
  InjectiveKanDiagram.localizedModelCategory SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono

/-- Its cofibrations and weak equivalences are the exact generic local classes. -/
theorem exactClasses :
    model.categoryWithCofibrations.cofibrations =
      (InjectiveKanDiagram.modelCategory
        SimplexCategoryᵒᵖ).categoryWithCofibrations.cofibrations ∧
    model.categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences localizingFamily :=
  InjectiveKanDiagram.localized_exactClasses SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono

/-- Localized fibrancy is precisely injective local-object fibrancy for this family. -/
theorem isFibrant_iff (W : Space) :
    @IsFibrant Space _ model.categoryWithFibrations _ W ↔
      Localization.localObject localizingFamily W :=
  InjectiveKanDiagram.localized_isFibrant_iff SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono W

#print axioms discrete_map_mono
#print axioms spineMap_mono
#print axioms completenessMap_mono
#print axioms localizerArrow_mono
#print axioms model
#print axioms exactClasses
#print axioms isFibrant_iff

end

end DaggerModels.PartII.OrdinaryCSSLocalization
