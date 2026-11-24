import DaggerModelsPartII.InjectiveKanDiagramDensity
import DaggerModelsPartII.ProjectiveWeakAccessibility
import DaggerModelsPartII.KanLeftProper
import OriginalSmithModelRecovered

/-! Smith recognition reduced to the exact density statement for the injective generators. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- The intended injective classes already satisfy the left-properness implication. -/
theorem classes_leftProper {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : cofibrations C i) (hk : weakEquivalences C k) : weakEquivalences C l := by
  letI : Mono i := hi
  intro c
  let E := (evaluation C SSet.{u}).obj c
  have hmono : Mono (i.app c) := inferInstance
  exact kanLeftProper (sq.map E)
    ((HomotopicalAlgebra.cofibration_iff _).mp
      (SSet.modelCategoryQuillen.cofibration_of_mono (i.app c))) (hk c)

/-- The one remaining generator-density equality needed for injective recognition. -/
def GeneratorsAreAllMonos : Prop :=
  (quotientSubobjectGenerators C).rlp.llp = cofibrations C

/-- The candidate generators have an actual small solution set against the
exact levelwise Kan weak-equivalence class. -/
def injectiveSolutionSet :
    DaggerSmithSolutionSet.SolutionData.{u} (quotientSubobjectGenerators C) (weakEquivalences C) :=
  ProjectiveKanDiagram.weakSolutionSet C _

theorem generators_rlp_le_weak (hgen : GeneratorsAreAllMonos C) :
    (quotientSubobjectGenerators C).rlp ≤ weakEquivalences C := by
  intro X Y p hp
  have hboundary : (ProjectiveKanDiagram.boundaryGenerators C).rlp p := by
    intro A B i hi
    have hmono : Mono i := (NatTrans.mono_iff_mono_app i).mpr
      (ProjectiveKanDiagram.boundaryCofibrations_levelwiseMono C i (le_llp_rlp _ i hi))
    have hleft : (quotientSubobjectGenerators C).rlp.llp i := hgen.symm ▸ hmono
    exact hleft p hp
  rw [ProjectiveKanDiagram.boundaryGenerators_rlp] at hboundary
  exact fun c ↦ (hboundary c).2

/-- All Smith inputs except generator density have already been proved.
Supplying that equality constructs the injective model data. -/
def smithData (hgen : GeneratorsAreAllMonos C) :
    DaggerSmithSolutionSet.CombinatorialData (injectiveSolutionSet C) := by
  letI := ProjectiveKanDiagram.locallyPresentable C
  letI : (weakEquivalences C).IsStableUnderRetracts := by
    change MorphismProperty.IsStableUnderRetracts
      ((HomotopicalAlgebra.weakEquivalences SSet.{u}).functorCategory C)
    infer_instance
  letI : MorphismProperty.IsStableUnderCobaseChange
      ((quotientSubobjectGenerators C).rlp.llp ⊓ weakEquivalences C) := by
    rw [hgen]
    change (trivialCofibrations C).IsStableUnderCobaseChange
    infer_instance
  letI : IsStableUnderTransfiniteComposition.{u}
      ((quotientSubobjectGenerators C).rlp.llp ⊓ weakEquivalences C) := by
    rw [hgen]
    change IsStableUnderTransfiniteComposition.{u} (trivialCofibrations C)
    constructor
    intro J _ _ _ _
    infer_instance
  exact DaggerSmithSolutionSet.combinatorialData (injectiveSolutionSet C)
    (generators_rlp_le_weak C hgen)

/-- The exact injective model, conditional only on the stated generator-density proof. -/
def modelOfGeneratorDensity (hgen : GeneratorsAreAllMonos C) : ModelCategory (C ⥤ SSet.{u}) :=
  (smithData C hgen).model

theorem modelOfGeneratorDensity_exactClasses (hgen : GeneratorsAreAllMonos C) :
    (modelOfGeneratorDensity C hgen).categoryWithCofibrations.cofibrations = cofibrations C ∧
      (modelOfGeneratorDensity C hgen).categoryWithWeakEquivalences.weakEquivalences =
        weakEquivalences C :=
  ⟨(smithData C hgen).modelCof.trans hgen, (smithData C hgen).modelWeak⟩

end

end DaggerModels.PartII.InjectiveKanDiagram
