import DaggerModelsPartII.DecoratedNecklaceHomDiagram
import NativeSimplicialReplacementWeightsChange
import NativeFamilyWeak
import ActualIteratedGadgetNecklaceComparison

/-!
# The actual decorated original-Hom simplicial-replacement span

The full natural left leg is Kan weak on the replacement diagonal. The
right leg is the augmentation of the full actual descended-label Hom
cocone. This retains every chain and its entire parameter simplex.

This is the bar of the actual decorated Hom diagram. It is NOT identified
with the ordered-label replacement diagonal or with the original JT flag
bar. The right augmentation is not asserted weak.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplicialReplacementWeightsChange
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedNecklaceHomBar

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedNecklaceHomDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- The full replacement diagonal of the original cylinder Hom diagram. -/
def cylinderBar : SSet.{0} :=
  DaggerBisimplicialDiagonal.diag (replacement (cylinderHomDiagram W x y))

/-- The full replacement diagonal of the original necklace Hom diagram. -/
def necklaceBar : SSet.{0} :=
  DaggerBisimplicialDiagonal.diag (replacement (necklaceHomDiagram W x y))

/-- The whole-diagonal left leg induced by the actual natural augmentation. -/
def leftBarMap : cylinderBar W x y ⟶ necklaceBar W x y :=
  diagonalChange (leftMap W x y)

private theorem leftChange_row (q : SimplexCategoryᵒᵖ) :
    (changeWeights (leftMap W x y)).app q =
      DaggerNativeFamilyWeak.familyMap
        (fun c : (nerve (Index W x y)).obj q ↦ (leftMap W x y).app (first c)) := by
  apply NatTrans.ext
  rfl

/-- The actual full decorated Hom bar left leg is Kan weak. -/
theorem leftBarMap_weak : WeakEquivalence (leftBarMap W x y) := by
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
  apply DaggerOriginalDiagonalGeometric.diagMap_geometric_row
  intro q
  rw [leftChange_row]
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  exact DaggerNativeFamilyWeak.familyMap_weak _ (fun c ↦ leftMap_weak W x y (first c))

/-- The retained original necklace endpoint Hom is weakly contractible,
including the zero-length code. This reuses the original level-zero gadget. -/
theorem necklaceHom_point_GW (T : DaggerChosenRigidificationNecklace.NecklaceCode) :
    DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.necklaceHom T)) :=
  DaggerActualIteratedGadgetNecklaceComparison.point_GW_of_toUnit
    (DaggerActualIteratedGadgetProperties.endpoint_hom_GW ⟨Sum.inl T, 0⟩)

/-- Projection retains the full actual decorated chain and forgets only its Hom simplex. -/
def necklaceProjection : necklaceBar W x y ⟶ nerve (Index W x y) :=
  diagonalProjection (necklaceHomDiagram W x y)

/-- The actual static-Hom bar projects weakly to the full decorated nerve. -/
theorem necklaceProjection_weak : WeakEquivalence (necklaceProjection W x y) := by
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
  exact diagonalProjection_GW (necklaceHomDiagram W x y)
    (fun i ↦ necklaceHom_point_GW
      (OrderedLabelElements.necklace W (boundaryPoint W x y) i))

/-- The analogous full-chain projection of the original cylinder-Hom bar. -/
def cylinderProjection : cylinderBar W x y ⟶ nerve (Index W x y) :=
  diagonalProjection (cylinderHomDiagram W x y)

/-- The two actual bar projections retain the SAME decorated chain. -/
theorem projection_square :
    leftBarMap W x y ≫ necklaceProjection W x y = cylinderProjection W x y :=
  DaggerNativeSimplicialReplacementWeightsChange.projection_square (leftMap W x y)

/-- The actual cylinder-Hom bar also projects weakly to that decorated nerve. -/
theorem cylinderProjection_weak : WeakEquivalence (cylinderProjection W x y) := by
  have : WeakEquivalence (leftBarMap W x y) := leftBarMap_weak W x y
  have : WeakEquivalence (necklaceProjection W x y) := necklaceProjection_weak W x y
  rw [← projection_square]
  infer_instance

/-- The full actual descended-label Hom cocone induces this right augmentation. -/
def evaluator : cylinderBar W x y ⟶ rawHom W x y :=
  diagonalAugmentation (cylinderHomDiagram W x y) (rightMap W x y)

/-- Inversion of the full left bar leg takes place only after Kan localization. -/
def leftBarIso :
    (weakEquivalences SSet.{0}).Q.obj (cylinderBar W x y) ≅
      (weakEquivalences SSet.{0}).Q.obj (necklaceBar W x y) := by
  have : WeakEquivalence (leftBarMap W x y) := leftBarMap_weak W x y
  have : IsIso ((weakEquivalences SSet.{0}).Q.map (leftBarMap W x y)) :=
    Localization.inverts _ _ _ (mem_weakEquivalences (leftBarMap W x y))
  exact asIso ((weakEquivalences SSet.{0}).Q.map (leftBarMap W x y))

/-- A whole-bar localized evaluator of the SAME decorated original-Hom span.
No weakness or comparison with either original target bar is inferred. -/
def localizedEvaluator :
    (weakEquivalences SSet.{0}).Q.obj (necklaceBar W x y) ⟶
      (weakEquivalences SSet.{0}).Q.obj (rawHom W x y) :=
  (leftBarIso W x y).inv ≫ (weakEquivalences SSet.{0}).Q.map (evaluator W x y)

end

end DaggerModels.PartII.DecoratedNecklaceHomBar
