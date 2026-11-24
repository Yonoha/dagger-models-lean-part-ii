import DaggerModelsPartII.DiagramHomKanFibration
import DaggerModelsPartII.MappingGeneratorLifting

/-! Weak-equivalence detection by derived mapping spaces from generator endpoints. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII.TargetResolution

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

noncomputable local instance detectionReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖᵒᵖ

/-- Derived mapping spaces from the cofibrant endpoints of generating cofibrations
detect weak equivalences between fibrant objects. -/
theorem weak_of_generator_derivedMapping
    [HasLimitsOfSize.{0, v} C]
    (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C) (hcofI : I ≤ cofibrations C)
    {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
    (hcof : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A ∧ IsCofibrant B)
    (hweak : ∀ {A B : C} (i : A ⟶ B), I i →
      weakEquivalences SSet.{v} ((cosimplicialResolution A).mappingSSet.map f) ∧
      weakEquivalences SSet.{v} ((cosimplicialResolution B).mappingSSet.map f)) :
    weakEquivalences C f := by
  let T : TargetResolution Y := cosimplicialResolution (op Y)
  obtain ⟨S, g, hg⟩ := T.exists_comparison_fibration f
  letI := S.fibrantOp
  letI := T.fibrantOp
  have hf : reedyMatchingProperty (fibrations Cᵒᵖᵒᵖ) g.mapOp := (fibration_iff _).mp hg
  have hS {s t : SimplexCategoryᵒᵖ} (k : s ⟶ t) :
      weakEquivalences Cᵒᵖᵒᵖ (S.oppositeDiagram.map k) := by
    rw [weakEquivalences_op, weakEquivalences_op]
    exact S.structureMap_weak k
  have hT {s t : SimplexCategoryᵒᵖ} (k : s ⟶ t) :
      weakEquivalences Cᵒᵖᵒᵖ (T.oppositeDiagram.map k) := by
    rw [weakEquivalences_op, weakEquivalences_op]
    exact T.structureMap_weak k
  refine weak_of_generator_mappingTests I hI f S T g hcof hweak ?_
  intro A B i hi
  haveI : IsCofibrant (op (op A)) := by
    apply (isCofibrant_iff_of_isInitial (initial.to A).op.op
      (initialOpOfTerminal (terminalOpOfInitial initialIsInitial))).mpr
    apply (cofibration_iff _).mpr
    rw [cofibrations_op, fibrations_op]
    letI := (hcof i hi).1
    exact mem_cofibrations (initial.to A)
  haveI : Cofibration i.op.op := by
    apply (cofibration_iff _).mpr
    rw [cofibrations_op, fibrations_op]
    exact hcofI _ hi
  exact ⟨(fibration_iff _).mp (diagramHomPostcomp_kan_fibration (op (op A)) hS hT g.mapOp hf),
    (fibration_iff _).mp (diagramHomCorner_kan_fibration i.op.op hS hT g.mapOp hf)⟩

end DaggerModels.PartII.TargetResolution
