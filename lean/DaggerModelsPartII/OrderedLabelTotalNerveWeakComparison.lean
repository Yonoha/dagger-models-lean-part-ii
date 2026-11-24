import DaggerModelsPartII.GrothendieckTotalElements
import DaggerModelsPartII.OrderedLabelNaturalWeakSpans
import DaggerModelsPartII.OrderedLabelSimplexResolution
import DaggerModelsPartII.GrothendieckNerveReplacement

/-!
# An actual weak zigzag from the original ordered-label bar to its decorated nerve

Every leg is the full original resolution, nerve, coordinate equivalence or
reversal comparison. The original necklace label and both operator directions
are retained. This is a SOURCE comparison; no evaluator/raw-unit weakness or
agreement with the separate first-object comparisonFunctor is inferred.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrderedLabelTotalNerveWeakComparison

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := NecklaceCode

variable (W : Source)
variable (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)

private abbrev L := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b
private abbrev F := GrothendieckTotalElements.elementDiagram (L W b)
private abbrev E := Grothendieck (F W b)

private def orderedToTotal : (OrderedLabelElements.labelPresheaf W b).Elements ⥤
    (GrothendieckTotalElements.totalDiagram (L W b)).Elements where
  obj i := ⟨(prodOpEquiv (C := NCode) (D := SimplexCategory)).functor.obj i.1, i.2⟩
  map f := ⟨(prodOpEquiv (C := NCode) (D := SimplexCategory)).functor.map f.val,
    f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem coordinate_unit :
    OrderedLabelSimplexResolution.totalToOrdered W b ⋙ orderedToTotal W b = 𝟭 _ := by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  case h_obj => rintro ⟨⟨T, k⟩, z⟩; rfl
  case h_map =>
    rintro ⟨⟨T, k⟩, z⟩ ⟨⟨U, l⟩, w⟩ f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

private theorem coordinate_counit :
    orderedToTotal W b ⋙ OrderedLabelSimplexResolution.totalToOrdered W b = 𝟭 _ := by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  case h_obj => rintro ⟨⟨T, k⟩, z⟩; rfl
  case h_map =>
    rintro ⟨⟨T, k⟩, z⟩ ⟨⟨U, l⟩, w⟩ f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- The actual original product/opposite coordinate functor has this exact inverse. -/
def coordinateEquivalence :
    (GrothendieckTotalElements.totalDiagram (L W b)).Elements ≌
      (OrderedLabelElements.labelPresheaf W b).Elements where
  functor := OrderedLabelSimplexResolution.totalToOrdered W b
  inverse := orderedToTotal W b
  unitIso := (eqToIso (coordinate_unit W b)).symm
  counitIso := eqToIso (coordinate_counit W b)

/-- The original degreewise-Elements Grothendieck construction, with exact total labels. -/
def totalEquivalence : E W b ≌ (OrderedLabelElements.labelPresheaf W b).Elements :=
  (GrothendieckTotalElements.equivalence (L W b)).trans (coordinateEquivalence W b)

/-- Taking opposites reaches the SAME accepted decorated label index. -/
def decoratedEquivalence : (E W b)ᵒᵖ ≌ OrderedLabelElements.Index W b :=
  (totalEquivalence W b).op

/-- The actual common source of the full original Grothendieck bar comparison. -/
def commonSource : SSet.{0} := GrothendieckNerveReplacement.commonSource (F W b)

/-- This leg retains the original entire degreewise-Elements nerve bar. -/
def toElementsBar : commonSource W b ⟶ OrderedLabelNaturalWeakSpans.elementsBar (L W b) :=
  GrothendieckNerveReplacement.toFiberBar (F W b)

theorem toElementsBar_weak : WeakEquivalence (toElementsBar W b) :=
  GrothendieckNerveReplacement.toFiberBar_weak (F W b)

def toTotalNerve : commonSource W b ⟶ nerve (E W b) :=
  GrothendieckNerveReplacement.toGrothendieck (F W b)

theorem toTotalNerve_weak : WeakEquivalence (toTotalNerve W b) :=
  GrothendieckNerveReplacement.toGrothendieck_weak (F W b)

/-- The original realization/singular object used solely to fix nerve orientation. -/
def realizedTotalNerve : SSet.{0} :=
  SSetReversalWeakSpan.comparisonTarget.obj (nerve (E W b))

def fromTotalNerve : nerve (E W b) ⟶ realizedTotalNerve W b :=
  SSetReversalWeakSpan.forward.app (nerve (E W b))

theorem fromTotalNerve_weak : WeakEquivalence (fromTotalNerve W b) :=
  SSetReversalWeakSpan.forward_weak _

/-- This exact decorated-index leg uses the actual inverse equivalence and nerve reversal. -/
def fromDecoratedNerve : nerve (OrderedLabelElements.Index W b) ⟶ realizedTotalNerve W b :=
  nerveMap (decoratedEquivalence W b).inverse ≫
    (DaggerNativeNerveOppositeIso.nerveOppositeIso (E W b)).inv ≫
      SSetReversalWeakSpan.reverse.app (nerve (E W b))

theorem fromDecoratedNerve_weak : WeakEquivalence (fromDecoratedNerve W b) := by
  have : WeakEquivalence (nerveMap (decoratedEquivalence W b).inverse) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have : WeakEquivalence (SSetReversalWeakSpan.reverse.app (nerve (E W b))) :=
    SSetReversalWeakSpan.reverse_weak _
  change WeakEquivalence (nerveMap (decoratedEquivalence W b).inverse ≫
    (DaggerNativeNerveOppositeIso.nerveOppositeIso (E W b)).inv ≫
      SSetReversalWeakSpan.reverse.app (nerve (E W b)))
  infer_instance

/-- One actual Kan weak arrow, before allowing either direction in the zigzag. -/
def weakArrow (X Y : SSet.{0}) : Prop := ∃ f : X ⟶ Y, WeakEquivalence f

/-- The ORIGINAL ordered-necklace-label bar and SAME decorated label nerve
are connected by the explicit eight-leg Kan weak zigzag, without W fibrancy. -/
theorem original_bar_to_decorated_weak_zigzag :
    Relation.EqvGen weakArrow (OrderedLabelSimplexResolution.bar W b)
      (nerve (OrderedLabelElements.Index W b)) := by
  apply Relation.EqvGen.trans (y := OrderedLabelNaturalWeakSpans.resolutionBar (L W b))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      ⟨OrderedLabelNaturalWeakSpans.toInput (L W b),
        OrderedLabelNaturalWeakSpans.toInput_weak (L W b)⟩)
  apply Relation.EqvGen.trans
    (y := OrderedLabelNaturalWeakSpans.oppositeElementsBar (L W b))
  · exact Relation.EqvGen.rel _ _
      ⟨OrderedLabelNaturalWeakSpans.toOppositeElements (L W b),
        OrderedLabelNaturalWeakSpans.toOppositeElements_weak (L W b)⟩
  apply Relation.EqvGen.trans
    (y := OrderedLabelNaturalWeakSpans.realizedElementsBar (L W b))
  · exact Relation.EqvGen.rel _ _
      ⟨OrderedLabelNaturalWeakSpans.oppositeToRealized (L W b),
        OrderedLabelNaturalWeakSpans.oppositeToRealized_weak (L W b)⟩
  apply Relation.EqvGen.trans (y := OrderedLabelNaturalWeakSpans.elementsBar (L W b))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      ⟨OrderedLabelNaturalWeakSpans.elementsToRealized (L W b),
        OrderedLabelNaturalWeakSpans.elementsToRealized_weak (L W b)⟩)
  apply Relation.EqvGen.trans (y := commonSource W b)
  · exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ ⟨toElementsBar W b, toElementsBar_weak W b⟩)
  apply Relation.EqvGen.trans (y := nerve (E W b))
  · exact Relation.EqvGen.rel _ _ ⟨toTotalNerve W b, toTotalNerve_weak W b⟩
  apply Relation.EqvGen.trans (y := realizedTotalNerve W b)
  · exact Relation.EqvGen.rel _ _ ⟨fromTotalNerve W b, fromTotalNerve_weak W b⟩
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ ⟨fromDecoratedNerve W b, fromDecoratedNerve_weak W b⟩)

end

end DaggerModels.PartII.OrderedLabelTotalNerveWeakComparison
