import DaggerModelsPartII.SimplicialResolutionFunctor
import DaggerModelsPartII.SSetReversalWeakSpan
import NativeSimplicialReplacementWeightsChange
import NativeFamilyWeak

/-!
# Natural entire-weight weak spans from original simplicial values to Elements nerves

The original resolution, exact opposite-Elements projection and actual weak
reversal cospans are natural BEFORE passing to full simplicial replacements.
No target evaluator or raw-unit weakness is inferred from the source spans.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplicialReplacementWeightsChange
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrderedLabelNaturalWeakSpans

noncomputable section

/-- The actual entire Elements nerves of the original simplicial values. -/
def elementsNerve : SSet.{0} ⥤ SSet.{0} := Functor.elementsFunctor ⋙ nerveFunctor

/-- The original realization/singular comparison of those same nerves. -/
def realizedElements : SSet.{0} ⥤ SSet.{0} :=
  elementsNerve ⋙ SSetReversalWeakSpan.comparisonTarget

/-- The existing natural nerve-op iso retains the same Elements category. -/
def oppositeIso : elementsNerve ⋙ SSet.opFunctor ≅
    SimplicialResolutionFunctor.elementsOpposite ⋙ nerveFunctor :=
  Functor.isoWhiskerLeft Functor.elementsFunctor
    DaggerNativeNerveOppositeIso.nerveOppositeNatIso

/-- The actual opposite-Elements nerve leg of the natural weak reversal cospan. -/
def fromOppositeElements :
    SimplicialResolutionFunctor.elementsOpposite ⋙ nerveFunctor ⟶ realizedElements :=
  oppositeIso.inv ≫ Functor.whiskerLeft elementsNerve SSetReversalWeakSpan.reverse

/-- The other actual leg uses the same original realization/singular unit. -/
def fromElements : elementsNerve ⟶ realizedElements :=
  Functor.whiskerLeft elementsNerve SSetReversalWeakSpan.forward

theorem fromOppositeElements_weak (X : SSet.{0}) :
    WeakEquivalence (fromOppositeElements.app X) := by
  have : WeakEquivalence (SSetReversalWeakSpan.reverse.app (elementsNerve.obj X)) :=
    SSetReversalWeakSpan.reverse_weak _
  change WeakEquivalence (oppositeIso.inv.app X ≫
    SSetReversalWeakSpan.reverse.app (elementsNerve.obj X))
  infer_instance

theorem fromElements_weak (X : SSet.{0}) : WeakEquivalence (fromElements.app X) :=
  SSetReversalWeakSpan.forward_weak _

variable {C : Type} [SmallCategory C]

/-- Entire simplicial replacements preserve actual componentwise Kan weak maps. -/
theorem diagonalChange_weak {G H : C ⥤ SSet.{0}} (η : G ⟶ H)
    (h : ∀ c, WeakEquivalence (η.app c)) : WeakEquivalence (diagonalChange η) := by
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
  apply DaggerOriginalDiagonalGeometric.diagMap_geometric_row
  intro q
  have hr : (changeWeights η).app q = DaggerNativeFamilyWeak.familyMap
      (fun c : (nerve C).obj q ↦ η.app (first c)) := by
    apply NatTrans.ext
    rfl
  rw [hr]
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
    (DaggerNativeFamilyWeak.familyMap_weak _ (fun c ↦ h (first c)))

variable (G : C ⥤ SSet.{0})

/-- The SAME full original input bar. -/
def inputBar : SSet.{0} := DaggerBisimplicialDiagonal.diag (replacement G)

def resolutionBar : SSet.{0} := DaggerBisimplicialDiagonal.diag
  (replacement (G ⋙ SimplicialResolutionFunctor.resolutionFunctor))

def oppositeElementsBar : SSet.{0} := DaggerBisimplicialDiagonal.diag
  (replacement (G ⋙ SimplicialResolutionFunctor.elementsOpposite ⋙ nerveFunctor))

def realizedElementsBar : SSet.{0} := DaggerBisimplicialDiagonal.diag
  (replacement (G ⋙ realizedElements))

def elementsBar : SSet.{0} := DaggerBisimplicialDiagonal.diag
  (replacement (G ⋙ elementsNerve))

/-- The literal full-input augmentation, on every whole chain and simplex. -/
def toInput : resolutionBar G ⟶ inputBar G :=
  diagonalChange (Functor.whiskerLeft G SimplicialResolutionFunctor.augmentation)

/-- The exact full opposite-Elements nerve comparison of the same original weights. -/
def toOppositeElements : resolutionBar G ⟶ oppositeElementsBar G :=
  diagonalChange (Functor.whiskerLeft G SimplicialResolutionFunctor.elementsProjection)

def oppositeToRealized : oppositeElementsBar G ⟶ realizedElementsBar G :=
  diagonalChange (Functor.whiskerLeft G fromOppositeElements)

def elementsToRealized : elementsBar G ⟶ realizedElementsBar G :=
  diagonalChange (Functor.whiskerLeft G fromElements)

theorem toInput_weak : WeakEquivalence (toInput G) :=
  diagonalChange_weak _ (fun c ↦ SimplicialResolutionFunctor.augmentation_weak (G.obj c))

theorem toOppositeElements_weak : WeakEquivalence (toOppositeElements G) :=
  diagonalChange_weak _
    (fun c ↦ SimplicialResolutionFunctor.elementsProjection_weak (G.obj c))

theorem oppositeToRealized_weak : WeakEquivalence (oppositeToRealized G) :=
  diagonalChange_weak _ (fun c ↦ fromOppositeElements_weak (G.obj c))

theorem elementsToRealized_weak : WeakEquivalence (elementsToRealized G) :=
  diagonalChange_weak _ (fun c ↦ fromElements_weak (G.obj c))

end

end DaggerModels.PartII.OrderedLabelNaturalWeakSpans
