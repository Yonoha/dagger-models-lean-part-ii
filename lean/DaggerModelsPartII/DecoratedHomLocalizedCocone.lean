import DaggerModelsPartII.DecoratedNecklaceHomBar
import DaggerModelsPartII.ReplacementConstantSections

/-!
# The original localized Hom components form a full natural cocone

The SAME original weak left maps are inverted only after Kan localization.
The whole-bar localized evaluator restricts to precisely these SAME component
maps. This is map coherence, not a proof that the evaluator is weak.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedHomLocalizedCocone

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedNecklaceHomDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Q := (weakEquivalences SSet.{0}).Q

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- The actual natural left leg becomes an iso of FULL localized diagrams. -/
def localizedLeftIso : cylinderHomDiagram W x y ⋙ Q ≅ necklaceHomDiagram W x y ⋙ Q :=
  NatIso.ofComponents (fun i ↦ by
    have : WeakEquivalence ((leftMap W x y).app i) := leftMap_weak W x y i
    have : IsIso (Q.map ((leftMap W x y).app i)) :=
      Localization.inverts Q (weakEquivalences SSet.{0}) _ (mem_weakEquivalences _)
    exact asIso (Q.map ((leftMap W x y).app i)))
    (fun f ↦ (Functor.whiskerRight (leftMap W x y) Q).naturality f)

/-- The original component span gives a cocone natural in BOTH operator axes. -/
def localizedRight : necklaceHomDiagram W x y ⋙ Q ⟶
    (Functor.const (Index W x y)).obj (Q.obj (rawHom W x y)) :=
  (localizedLeftIso W x y).inv ≫ Functor.whiskerRight (rightMap W x y) Q
    ≫ (Functor.constComp (Index W x y) (rawHom W x y) Q).hom

/-- Every cocone leg is the SAME previously checked localized component map. -/
theorem localizedRight_app (i : Index W x y) :
    (localizedRight W x y).app i =
      NecklaceCylinderHomSpan.localizedComponent W x y
        (OrderedLabelElements.necklace W (boundaryPoint W x y) i)
        (OrderedLabelElements.degree W (boundaryPoint W x y) i)
        (OrderedLabelElements.label W (boundaryPoint W x y) i) := by
  dsimp only [localizedRight, NatTrans.comp_app, Functor.constComp_hom_app]
  rw [Category.comp_id]
  rfl

/-- Full naturality retains the original decorated-index Hom map. -/
theorem localizedRight_natural {i j : Index W x y} (f : i ⟶ j) :
    Q.map ((necklaceHomDiagram W x y).map f) ≫ (localizedRight W x y).app j =
      (localizedRight W x y).app i := by
  have h := (localizedRight W x y).naturality f
  change Q.map ((necklaceHomDiagram W x y).map f) ≫ (localizedRight W x y).app j =
    (localizedRight W x y).app i ≫ 𝟙 (Q.obj (rawHom W x y)) at h
  exact h.trans (Category.comp_id _)

private theorem section_left_square (i : Index W x y) :
    Q.map (ReplacementConstantSections.sectionMap (cylinderHomDiagram W x y) i) ≫
        (DecoratedNecklaceHomBar.leftBarIso W x y).hom =
      (localizedLeftIso W x y).hom.app i ≫
        Q.map (ReplacementConstantSections.sectionMap (necklaceHomDiagram W x y) i) := by
  change Q.map _ ≫ Q.map (DecoratedNecklaceHomBar.leftBarMap W x y) =
    Q.map ((leftMap W x y).app i) ≫ Q.map _
  rw [← Q.map_comp, ← Q.map_comp]
  exact congrArg Q.map (ReplacementConstantSections.section_change (leftMap W x y) i)

private theorem inverse_section_square (i : Index W x y) :
    Q.map (ReplacementConstantSections.sectionMap (necklaceHomDiagram W x y) i) ≫
        (DecoratedNecklaceHomBar.leftBarIso W x y).inv =
      (localizedLeftIso W x y).inv.app i ≫
        Q.map (ReplacementConstantSections.sectionMap (cylinderHomDiagram W x y) i) := by
  apply (cancel_mono (DecoratedNecklaceHomBar.leftBarIso W x y).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [section_left_square, ← Category.assoc, Iso.inv_hom_id_app]
  exact (Category.id_comp _).symm

/-- The WHOLE original localized bar evaluator restricts to its SAME component.
Both necklace and simplex operators remain in the natural cocone above. -/
theorem whole_bar_component (i : Index W x y) :
    Q.map (ReplacementConstantSections.sectionMap (necklaceHomDiagram W x y) i) ≫
        DecoratedNecklaceHomBar.localizedEvaluator W x y =
      (localizedRight W x y).app i := by
  dsimp only [DecoratedNecklaceHomBar.localizedEvaluator]
  rw [← Category.assoc, inverse_section_square, Category.assoc, ← Q.map_comp]
  change (localizedLeftIso W x y).inv.app i ≫
    Q.map (ReplacementConstantSections.sectionMap (cylinderHomDiagram W x y) i ≫
      DaggerNativeSimplicialReplacement.diagonalAugmentation (cylinderHomDiagram W x y)
        (rightMap W x y)) = _
  rw [ReplacementConstantSections.section_augmentation]
  dsimp only [localizedRight, NatTrans.comp_app, Functor.constComp_hom_app]
  rw [Category.comp_id]
  rfl

end

end DaggerModels.PartII.DecoratedHomLocalizedCocone
