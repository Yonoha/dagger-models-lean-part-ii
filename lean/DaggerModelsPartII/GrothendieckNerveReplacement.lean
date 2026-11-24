import DaggerModelsPartII.TheoremAReplacementComparison
import DaggerModelsPartII.GrothendieckCommaRetraction
import NativeSimplicialReplacementWeightsChange
import NativeFamilyWeak

/-!
# A full native weak span from a category-diagram bar to its Grothendieck nerve

The exact original comma-weight replacement is the common source. One leg
uses the natural comma-to-fiber retraction, the other the unconditional
original Theorem A augmentation. Every entire chain and simplex is retained.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplicialReplacementWeightsChange
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.GrothendieckNerveReplacement

noncomputable section

variable {C : Type u} [Category.{u} C] (F : C ⥤ Cat.{u,u})

/-- The original diagram's entire nerves. -/
def fiberNerves : C ⥤ SSet.{u} := F ⋙ nerveFunctor

/-- The actual comma weights of the same Grothendieck projection. -/
def commaNerves : C ⥤ SSet.{u} :=
  TheoremAReplacementComparison.commaNerves (Grothendieck.forget F)

/-- The SAME natural comma retraction, on the whole original nerve diagrams. -/
def weightMap : commaNerves F ⟶ fiberNerves F :=
  Functor.whiskerRight (GrothendieckCommaRetraction.retraction F) nerveFunctor

/-- The common source retains all original comma chains and whole simplices. -/
def commonSource : SSet.{u} := DaggerBisimplicialDiagonal.diag (replacement (commaNerves F))

/-- The full original simplicial-replacement diagonal of the category diagram. -/
def fiberBar : SSet.{u} := DaggerBisimplicialDiagonal.diag (replacement (fiberNerves F))

/-- The actual left leg on the full replacement diagonal. -/
def toFiberBar : commonSource F ⟶ fiberBar F := diagonalChange (weightMap F)

private theorem change_row (q : SimplexCategoryᵒᵖ) :
    (changeWeights (weightMap F)).app q =
      DaggerNativeFamilyWeak.familyMap
        (fun c : (nerve C).obj q ↦ (weightMap F).app (first c)) := by
  apply NatTrans.ext
  rfl

/-- The entire natural left leg is Kan weak; no contractibility of fibers is assumed. -/
theorem toFiberBar_weak : WeakEquivalence (toFiberBar F) := by
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
  apply DaggerOriginalDiagonalGeometric.diagMap_geometric_row
  intro q
  rw [change_row]
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  exact DaggerNativeFamilyWeak.familyMap_weak _
    (fun c ↦ GrothendieckCommaRetraction.retract_weak F (first c))

/-- The actual original Theorem A leg to the SAME Grothendieck nerve. -/
def toGrothendieck : commonSource F ⟶ nerve (Grothendieck F) :=
  TheoremAReplacementComparison.augmentation (Grothendieck.forget F)

/-- The entire other leg is Kan weak without any fibrancy or nonempty-fiber premise. -/
theorem toGrothendieck_weak : WeakEquivalence (toGrothendieck F) :=
  TheoremAReplacementComparison.augmentation_weak (Grothendieck.forget F)

end

end DaggerModels.PartII.GrothendieckNerveReplacement
