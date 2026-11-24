import DaggerModelsPartII.JTBarProjectivePushout
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Projective cofibrancy of the actual full reversal-index bar

Use the actual successor pushouts and actual skeletal colimit. Each attaching
map is a coproduct of original free boundary generators. Native lifting-class
closure under coproducts, cobase change and countable composition gives the
cofibrancy of the original bar, including its restriction to dagger inputs.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTBarProjectiveCofibrancy

open JTProjectiveBar JTBarProjectiveCells JTBarProjectivePushout

noncomputable section

private abbrev I := ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ

/-- The actual full-label free boundary coproduct is in the original projective
cofibration class, by the existing coproduct lifting property. -/
theorem attachingBoundaryMap_cofibration (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    I.rlp.llp (attachingBoundaryMap P r) := by
  intro X Y p hp
  have : ∀ t : JTBarNondegenerateCells.NondegenerateLabel P r,
      HasLiftingProperty
        ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ (op t.1.1.left)).map
          (SSet.boundary r).ι) p := fun t ↦ hp _ ⟨(op t.1.1.left, r)⟩
  change HasLiftingProperty
    (Limits.Sigma.map (fun t : JTBarNondegenerateCells.NondegenerateLabel P r ↦
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ (op t.1.1.left)).map
        (SSet.boundary r).ι)) p
  infer_instance

/-- Every actual skeletal successor map is projectively cofibrant. -/
theorem barSkeletonMap_cofibration (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    I.rlp.llp (barSkeletonMap P (Nat.le_succ r)) :=
  I.rlp.llp.of_isPushout (attaching_isPushout P r)
    (attachingBoundaryMap_cofibration P r)

/-- The original inclusion from the zero skeleton is the actual countable
composition of the free projective boundary attachments. -/
def barSkeletonIncl_zero_transfinite (P : ReverseSimplexᵒᵖ ⥤ Type) :
    I.rlp.llp.TransfiniteCompositionOfShape ℕ (barSkeletonIncl P 0) where
  F := barSkeletalDiagram P
  isoBot := Iso.refl _
  incl := (barSkeletalCocone P).ι
  isColimit := barSkeletalCocone_isColimit P
  fac := Category.id_comp _
  map_mem n _ := barSkeletonMap_cofibration P n

/-- The actual zero-to-bar inclusion is an original projective cofibration. -/
theorem barSkeletonIncl_zero_cofibration (P : ReverseSimplexᵒᵖ ⥤ Type) :
    I.rlp.llp (barSkeletonIncl P 0) :=
  I.rlp.llp.transfiniteCompositionsOfShape_le ℕ _
    ⟨barSkeletonIncl_zero_transfinite P⟩

/-- The full original bar is cofibrant in the actual projective Kan diagram model. -/
theorem barPresheaf_isCofibrant (P : ReverseSimplexᵒᵖ ⥤ Type) :
    (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsCofibrant (barPresheaf P)) := by
  letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have h : Cofibration (barSkeletonIncl P 0) := by
    rw [cofibration_iff, ProjectiveKanDiagram.model_cofibrations]
    exact barSkeletonIncl_zero_cofibration P
  exact (isCofibrant_iff_of_isInitial _ (barSkeletonZeroIsInitial P)).mpr h

/-- In particular, the literal bar on every original dagger simplicial set is
projectively cofibrant; no replacement by a different resolution is made. -/
theorem barOnDagger_isCofibrant (X : DaggerSSet.{0}) :
    (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsCofibrant (barOnDagger.obj X)) :=
  barPresheaf_isCofibrant (DaggerSSet.toPresheaf.obj X)

/-- The original augmentation is weak in this same projective Kan model,
using the retained rowwise contraction rather than a new augmentation. -/
theorem barAugmentation_weak (X : DaggerSSet.{0}) :
    (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      weakEquivalences (ReverseSimplexᵒᵖ ⥤ SSet.{0}) (barAugmentation.app X)) := by
  letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  rw [ProjectiveKanDiagram.model_weakEquivalences]
  intro d
  exact (weakEquivalence_iff _).1
    ((DaggerSSetGluing.weakEquivalence_iff_GW _).2 (barAugmentation_rowwise_GW X d))

/-- The actual bar is a projectively cofibrant resolution of the literal
constant-vertex diagram. No fibration or weak derived beta is asserted. -/
theorem barOnDagger_cofibrant_and_augmentation_weak (X : DaggerSSet.{0}) :
    (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsCofibrant (barOnDagger.obj X) ∧
        weakEquivalences (ReverseSimplexᵒᵖ ⥤ SSet.{0}) (barAugmentation.app X)) :=
  ⟨barOnDagger_isCofibrant X, barAugmentation_weak X⟩

end

end DaggerModels.PartII.JTBarProjectiveCofibrancy
