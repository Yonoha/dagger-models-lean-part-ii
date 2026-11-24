import DaggerModelsPartII.ReplacementTotalElements
import DaggerModelsPartII.OrderedLabelElements
import NativeSimplexIndexNerveWeakContractibility
import NativeGroupoidCompletionNerveBaseCases
import NativeDualTheoremA

/-!
# The original ordered-label bar, its simplex resolution and actual total-label map

Both legs of the standard simplex resolution are weak. The actual map from
bar simplices to the unchanged decorated index is constructed explicitly.
Its nerve weakness still requires the stated actual comma-nerve contraction;
neither that premise nor raw-unit/gTilde weakness is proved in this module.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerNativeSimplicialReplacement
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrderedLabelSimplexResolution

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := NecklaceCode

variable (W : Source)
variable (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)

private abbrev L := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b

/-- The SAME original ordered-label replacement diagonal. -/
abbrev bar : SSet.{0} := ReplacementTotalElements.bar (L W b)

/-- Only the product/opposite coordinate convention is changed. -/
def totalToOrdered :
    (ReplacementTotalElements.totalPresheaf (L W b)).Elements ⥤
      (OrderedLabelElements.labelPresheaf W b).Elements where
  obj i := ⟨op (i.1.1.unop, i.1.2.unop), i.2⟩
  map f := ⟨(prodOpEquiv (C := NCode) (D := SimplexCategory)).inverse.map f.val,
    f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual total-label functor retains both operators and the original label. -/
def comparisonFunctor :
    (bar W b).Elementsᵒᵖ ⥤ OrderedLabelElements.Index W b :=
  (ReplacementTotalElements.toTotal (L W b) ⋙ totalToOrdered W b).op

/-- On every original bar simplex, the image is its actual first label. -/
theorem comparisonFunctor_obj (q : SimplexCategoryᵒᵖ)
    (c : (nerve NCodeᵒᵖ).obj q)
    (z : ((L W b).obj (DaggerNativeSimplicialReplacementCells.first c)).obj q) :
    (comparisonFunctor W b).obj (op ((bar W b).elementsMk q ⟨c, z⟩)) =
      OrderedLabelElements.mk W b (c.obj 0).unop q.unop z := rfl

/-- Mathlib's actual elements/simplex-index equivalence, with the pinned Yoneda. -/
def simplexElementsEquiv :
    (bar W b).Elementsᵒᵖ ≌ DaggerNativeSimplexIndexResolution.Index (bar W b) :=
  CategoryOfElements.costructuredArrowULiftYonedaEquivalence (bar W b)

/-- The existing standard-simplex resolution of the ORIGINAL ordered-label bar. -/
def resolution : SSet.{0} :=
  DaggerBisimplicialDiagonal.diag (DaggerNativeSimplexIndexResolution.resolution (bar W b))

/-- The original full-simplex augmentation, without replacing it by endpoint values. -/
def toBar : resolution W b ⟶ bar W b :=
  DaggerNativeSimplexIndexResolution.toOriginal (bar W b)

/-- This leg is weak without any fibrancy assumption on the original W. -/
theorem toBar_weak : WeakEquivalence (toBar W b) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNativeSimplexIndexNerveWeakContractibility.toOriginal_GW (bar W b))

/-- The other standard-resolution leg, to the actual opposite Elements nerve. -/
def toBarElements : resolution W b ⟶ nerve (bar W b).Elementsᵒᵖ :=
  DaggerNativeSimplexIndexResolution.toNerve (bar W b) ≫
    nerveMap (simplexElementsEquiv W b).inverse

/-- This exact full-index leg is weak by the native resolution and Mathlib equivalence. -/
theorem toBarElements_weak : WeakEquivalence (toBarElements W b) := by
  have : WeakEquivalence (DaggerNativeSimplexIndexResolution.toNerve (bar W b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerNativeSimplexIndexResolution.toNerve_GW (bar W b))
  have : WeakEquivalence (nerveMap (simplexElementsEquiv W b).inverse) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  change WeakEquivalence (DaggerNativeSimplexIndexResolution.toNerve (bar W b) ≫ _)
  infer_instance

/-- An actual candidate comparison to the SAME original decorated label nerve. -/
def toOrderedElements : resolution W b ⟶ nerve (OrderedLabelElements.Index W b) :=
  toBarElements W b ≫ nerveMap (comparisonFunctor W b)

/-- The actual candidate is weak exactly when its actual total-label functor is.
This is a reduction, not a proof of that remaining weakness. -/
theorem toOrderedElements_weak_iff :
    WeakEquivalence (toOrderedElements W b) ↔
      WeakEquivalence (nerveMap (comparisonFunctor W b)) := by
  have : WeakEquivalence (toBarElements W b) := toBarElements_weak W b
  exact (weakEquivalence_precomp_iff (toBarElements W b)
    (nerveMap (comparisonFunctor W b)))

/-- Native dual Quillen A retains the exact missing StructuredArrow contraction.
No nonemptiness or generic finality assertion replaces this hypothesis. -/
theorem toOrderedElements_weak_of_comma
    (h : ∀ d : OrderedLabelElements.Index W b,
      DaggerSSetGluing.GW (DaggerOriginalProductGadget.pointMap
        (nerve (StructuredArrow d (comparisonFunctor W b))))) :
    WeakEquivalence (toOrderedElements W b) := by
  apply (toOrderedElements_weak_iff W b).mpr
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNativeDualTheoremA.nerveMap_GW (comparisonFunctor W b) h)

end

end DaggerModels.PartII.OrderedLabelSimplexResolution
