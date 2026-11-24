import DaggerModelsPartII.InjectiveKanDiagramGeneration
import DaggerModelsPartII.InjectiveTensorMapping
import DaggerModelsPartII.InjectiveStandardFrame
import DaggerModelsPartII.InjectiveMappingResolution

/-!
# The injective Kan model on simplicial-set diagrams

The quotient-subobject generators generate all monomorphisms. Smith recognition
therefore gives the injective model with precisely the intended classes.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- The generator-density input to injective recognition is a proved equality. -/
theorem generatorsAreAllMonos : GeneratorsAreAllMonos C :=
  quotientGeneratedCofibrations_eq_cofibrations C

/-- The locally presentable category, small generating families, and Smith model data. -/
def combinatorialData :
    DaggerSmithSolutionSet.CombinatorialData (injectiveSolutionSet C) :=
  smithData C (generatorsAreAllMonos C)

/-- The injective Kan model structure on diagrams indexed by a small category. -/
def modelCategory : ModelCategory (C ⥤ SSet.{u}) :=
  (combinatorialData C).model

local instance recognizedInjectiveModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- Injective cofibrations are exactly monomorphisms of diagrams. -/
theorem model_cofibrations :
    HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) = monomorphisms _ :=
  (modelOfGeneratorDensity_exactClasses C (generatorsAreAllMonos C)).1

/-- Injective weak equivalences are exactly levelwise Kan weak equivalences. -/
theorem model_weakEquivalences :
    HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) =
      (HomotopicalAlgebra.weakEquivalences SSet.{u}).functorCategory C :=
  (modelOfGeneratorDensity_exactClasses C (generatorsAreAllMonos C)).2

/-- Local presentability and two small generating families for the injective model. -/
theorem combinatorial :
    IsLocallyPresentable.{u} (C ⥤ SSet.{u}) ∧
      ∃ I J : MorphismProperty (C ⥤ SSet.{u}),
        IsSmall.{u} I ∧ IsSmall.{u} J ∧
          HasSmallObjectArgument.{u} I ∧ HasSmallObjectArgument.{u} J ∧
          I.rlp.llp = HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ∧
          J.rlp.llp = HomotopicalAlgebra.trivialCofibrations (C ⥤ SSet.{u}) := by
  let d := combinatorialData C
  letI := d.locallyPresentable
  letI := d.smallI
  letI := d.smallJ
  refine ⟨d.locallyPresentable, quotientSubobjectGenerators C,
    DaggerSmithSolutionSet.J (injectiveSolutionSet C), d.smallI, d.smallJ,
    DaggerSmithSolutionSet.smallObjectArgument _,
    DaggerSmithSolutionSet.smallObjectArgument _, ?_, ?_⟩
  · exact d.modelCof.symm
  · change _ = d.model.categoryWithCofibrations.cofibrations ⊓
      d.model.categoryWithWeakEquivalences.weakEquivalences
    rw [d.modelCof, d.modelWeak]
    exact d.trivialCofibrations

/-- Every object of the injective model is cofibrant. -/
theorem model_isCofibrant (A : C ⥤ SSet.{u}) : IsCofibrant A := by
  letI : Fact (GeneratorsAreAllMonos C) := ⟨generatorsAreAllMonos C⟩
  exact everyObject_isCofibrant C A

/-- The injective Kan model is left proper. -/
theorem model_leftProper {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i)
    (hk : HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) k) :
    HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) l := by
  rw [model_cofibrations] at hi
  rw [model_weakEquivalences] at hk ⊢
  exact classes_leftProper C sq hi hk

/-- Tensor and strict mapping space are Quillen adjoints for every fixed diagram. -/
theorem model_tensorMapping_isQuillen (A : C ⥤ SSet.{u}) :
    (diagramTensorMappingAdjunction A).IsQuillenAdjunction := by
  letI : Fact (GeneratorsAreAllMonos C) := ⟨generatorsAreAllMonos C⟩
  exact diagramTensorMapping_isQuillen C A

/-- An injectively fibrant target has Kan strict mapping space from every diagram. -/
theorem model_mappingSpace_isFibrant (A W : C ⥤ SSet.{u}) [IsFibrant W] :
    IsFibrant (diagramMappingSpace A W) := by
  letI : Fact (GeneratorsAreAllMonos C) := ⟨generatorsAreAllMonos C⟩
  exact diagramMappingSpace_isFibrant C A W

/-- The strict mapping-space test computes the derived test in the injective model. -/
theorem model_homotopyMapping_iff_strict {A B W : C ⥤ SSet.{u}} [IsFibrant W]
    (f : A ⟶ B) :
    homotopyMappingWeakEquivalences W f ↔
      HomotopicalAlgebra.weakEquivalences SSet.{u} (diagramMappingPrecomp f W) := by
  letI : Fact (GeneratorsAreAllMonos C) := ⟨generatorsAreAllMonos C⟩
  exact homotopyMappingWeakEquivalences_iff_strict C f

/-- The chosen homotopy function complex maps to the strict mapping space. -/
def model_chosenMappingToStrict (A W : C ⥤ SSet.{u}) :
    (cosimplicialResolution A).mappingSSet.obj W ⟶ diagramMappingSpace A W := by
  letI : Fact (GeneratorsAreAllMonos C) := ⟨generatorsAreAllMonos C⟩
  exact chosenMappingToStrict C A W

/-- This comparison is a weak equivalence for every injectively fibrant target. -/
theorem model_chosenMappingToStrict_weak (A W : C ⥤ SSet.{u}) [IsFibrant W] :
    HomotopicalAlgebra.weakEquivalences SSet.{u} (model_chosenMappingToStrict C A W) := by
  letI : Fact (GeneratorsAreAllMonos C) := ⟨generatorsAreAllMonos C⟩
  exact chosenMappingToStrict_weak C A W

end

end DaggerModels.PartII.InjectiveKanDiagram
