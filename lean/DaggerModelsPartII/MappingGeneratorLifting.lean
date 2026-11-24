import DaggerModelsPartII.DerivedMappingTwoResolutions
import DaggerModelsPartII.RelativeDiagramHom

/-! Reduction of derived weak-equivalence detection to the Kan fibration tests on a
comparison of target resolutions. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII.TargetResolution

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

/-- The actual generator test. Once the mapping-space fibration conditions for the
right resolutions hold, weak equivalences on the generator endpoints give strict
lifting against the same generators in degree zero. -/
theorem weak_of_generator_mappingTests
    (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
    (S : TargetResolution X) (T : TargetResolution Y) (g : T.Comparison S f.op)
    (hcof : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A ∧ IsCofibrant B)
    (hweak : ∀ {A B : C} (i : A ⟶ B), I i →
      weakEquivalences SSet.{v} ((cosimplicialResolution A).mappingSSet.map f) ∧
      weakEquivalences SSet.{v} ((cosimplicialResolution B).mappingSSet.map f))
    (hKan : ∀ {A B : C} (i : A ⟶ B), I i →
      fibrations SSet.{v} (diagramHomPostcomp (op (op A)) g.mapOp) ∧
      fibrations SSet.{v} (diagramHomCorner i.op.op g.mapOp)) :
    weakEquivalences C f := by
  let z := op ⦋0⦌
  let p := (g.mapOp.app z).unop.unop
  have hp : I.rlp p := by
    intro A B i hi
    obtain ⟨ha, hb⟩ := hcof i hi
    letI := ha
    letI := hb
    have hA : weakEquivalences SSet.{v} (diagramHomPostcomp (op (op A)) g.mapOp) :=
      (mappingSSet_map_weak_iff (cosimplicialResolution A) S T f g).mp (hweak i hi).1
    have hB : weakEquivalences SSet.{v} (diagramHomPostcomp (op (op B)) g.mapOp) :=
      (mappingSSet_map_weak_iff (cosimplicialResolution B) S T f g).mp (hweak i hi).2
    have hf := hKan i hi
    exact (hasLiftingProperty_evalZero_of_mappingTests i.op.op g.mapOp
      ⟨hf.1, hA⟩ hB hf.2).unop.unop
  rw [hI] at hp
  have ha := S.augmentation_weak z
  have hb := T.augmentation_weak z
  rw [weakEquivalences_op] at ha hb
  have w := congrArg (fun k ↦ Quiver.Hom.unop (Quiver.Hom.unop k)) (congr_app g.comm z)
  change (S.augmentationOp.app z).unop.unop ≫ p =
    f ≫ (T.augmentationOp.app z).unop.unop at w
  exact (weakEquivalences C).of_postcomp _ _ hb
    (w ▸ (weakEquivalences C).comp_mem _ _ ha hp.2)

end DaggerModels.PartII.TargetResolution
