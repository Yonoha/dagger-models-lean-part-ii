import DaggerModelsPartII.HomotopyMappingEquivalence
import DaggerModelsPartII.DiagramHomKanFibration

/-! Resolution comparisons whose mapping-space tests are fibrations. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII.CosimplicialResolution

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

noncomputable local instance sourceComparisonReedyModel :
    ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

/-- After fixing the resolution of the source, the resolution of the codomain can
be chosen so that the opposite comparison is a Reedy fibration. -/
theorem exists_comparison_reedyFibration {X Y : C} (R : CosimplicialResolution X) (f : X ⟶ Y) :
    ∃ (S : CosimplicialResolution Y) (g : R.Comparison S f),
      reedyMatchingProperty (fibrations Cᵒᵖ) g.mapOp := by
  let a := (Functor.const SimplexCategoryᵒᵖ).map f.op ≫ R.augmentationOp
  let d := factorizationData (trivialCofibrations _) (fibrations _) a
  letI := R.fibrantOp
  letI : Fibration d.p := (fibration_iff _).mpr d.hp
  let S : CosimplicialResolution Y := ⟨d.Z, d.i, d.hi, isFibrant_of_fibration d.p⟩
  exact ⟨S, ⟨d.p, d.fac⟩, d.hp⟩

private theorem resolution_structureMap_weak {X : C} (R : CosimplicialResolution X)
    {s t : SimplexCategoryᵒᵖ} (k : s ⟶ t) :
    weakEquivalences Cᵒᵖ (R.oppositeDiagram.map k) := by
  have hs : weakEquivalences Cᵒᵖ (R.augmentationOp.app s) := R.augmentation_weak s
  have ht : weakEquivalences Cᵒᵖ (R.augmentationOp.app t) := R.augmentation_weak t
  have h := R.augmentationOp.naturality k
  change 𝟙 (op X) ≫ R.augmentationOp.app t =
    R.augmentationOp.app s ≫ R.oppositeDiagram.map k at h
  rw [Category.id_comp] at h
  exact (weakEquivalences Cᵒᵖ).of_precomp _ _ hs (h ▸ ht)

/-- For a fibrant target, the chosen Reedy fibration comparison gives a Kan
fibration of the derived mapping simplicial sets. -/
theorem Comparison.precomp_fibration [HasColimitsOfSize.{0, v} C]
    {X Y : C} {R : CosimplicialResolution X} {S : CosimplicialResolution Y} {f : X ⟶ Y}
    (g : R.Comparison S f) (hg : reedyMatchingProperty (fibrations Cᵒᵖ) g.mapOp)
    (Z : C) [IsFibrant Z] : Fibration (g.precomp Z) := by
  letI := S.fibrantOp
  letI := R.fibrantOp
  letI : IsCofibrant (op Z) := by
    apply (isCofibrant_iff_of_isInitial (terminal.from Z).op (initialOpOfTerminal terminalIsTerminal)).mpr
    exact (cofibration_op_iff _).mpr inferInstance
  exact diagramHomPostcomp_kan_fibration (op Z)
    (resolution_structureMap_weak S) (resolution_structureMap_weak R) g.mapOp hg

/-- A local equivalence, tested against a fixed fibrant target, gives a Kan trivial
fibration for a Reedy fibration comparison of its source resolutions. -/
theorem Comparison.precomp_trivialFibration_of_test [HasColimitsOfSize.{0, v} C]
    {X Y : C} {R : CosimplicialResolution X} {S : CosimplicialResolution Y} {f : X ⟶ Y}
    (g : R.Comparison S f) (hg : reedyMatchingProperty (fibrations Cᵒᵖ) g.mapOp)
    (Z : C) [IsFibrant Z] (hf : homotopyMappingWeakEquivalences Z f) :
    trivialFibrations SSet.{v} (g.precomp Z) :=
  ⟨(fibration_iff _).mp (g.precomp_fibration hg Z), (homotopyMappingWeakEquivalences_iff Z g).mp hf⟩

end DaggerModels.PartII.CosimplicialResolution
