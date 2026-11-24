import DaggerModelsPartII.OrderedNecklaceLabelDiagram
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying

/-!
# The actual decorated category of ordered necklace labels

An object records the original native necklace, simplex degree and label.
Morphisms retain both operators and their exact presheaf equation. No
contractibility, finality or comparison with a bar diagonal is asserted here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.OrderedLabelElements

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := NecklaceCode

/-- The original ordered labels, uncurried in their two contravariant axes. -/
def labelPresheaf (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W) :
    (NCode × SimplexCategory)ᵒᵖ ⥤ Type :=
  (prodOpEquiv NCode (D := SimplexCategory)).functor ⋙
    Functor.uncurry.obj (OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b)

/-- The opposite of the actual category of elements gives forward operators. -/
abbrev Index (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W) :=
  (labelPresheaf W b).Elementsᵒᵖ

/-- Projection retains BOTH native necklace and simplex operators. -/
def projection (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W) :
    Index W b ⥤ NCode × SimplexCategory :=
  (CategoryOfElements.π (labelPresheaf W b)).leftOp

/-- The actual native necklace of a decorated label. -/
def necklace (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : Index W b) : NCode := ((projection W b).obj i).1

/-- The actual parameter degree of a decorated label. -/
def degree (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : Index W b) : SimplexCategory := ((projection W b).obj i).2

/-- The label is unchanged; no replacement simplex is chosen. -/
def label (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : Index W b) :
    ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).obj
      (op (necklace W b i))).obj (op (degree W b i)) := i.unop.2

/-- An original ordered-label simplex gives its actual decorated object. -/
def mk (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (T : NCode) (k : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).obj (op T)).obj
      (op k)) : Index W b :=
  op ((labelPresheaf W b).elementsMk (op (T, k)) z)

/-- Every decorated arrow obeys the exact ordered-label equation in both axes. -/
theorem label_map (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    {i j : Index W b} (f : i ⟶ j) :
    ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).obj
        (op (necklace W b i))).map ((projection W b).map f).2.op
      (((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).map
        ((projection W b).map f).1.op).app (op (degree W b j)) (label W b j)) =
      label W b i :=
  f.unop.property

end

end DaggerModels.PartII.OrderedLabelElements
