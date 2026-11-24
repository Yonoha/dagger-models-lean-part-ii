import DaggerModelsPartII.JTOrderedLabelPaddingPrismSliceArrow
import DaggerModelsPartII.JTParametrizedTargetRelabel

/-! Transport the original fixed-target graph family along a preserved time slice. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismTarget

open OrderedNecklaceVertexPoints (boundaryPoint)
open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (Family codes)
open JTOrderedLabelPaddingPrismSliceArrow (originalBase TimeSection comparison)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A B : Type} [SmallCategory A] [SmallCategory B] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time)

private abbrev b := boundaryPoint W x y
private abbrev E := (JTOrderedLabelPaddingPrismDiagram.mixed W (b (W := W) (x := x) (y := y)) L).Elementsᵒᵖ

variable (H : B ⥤ E (L := L))
variable (t : TimeSection W (b (W := W) (x := x) (y := y)) L H)

private abbrev p := H ⋙ originalBase W (b (W := W) (x := x) (y := y)) L
private abbrev old := p H ⋙ L
private abbrev realized :=
  H ⋙ JTOrderedLabelPaddingPrismLabels.labelIndex W (b (W := W) (x := x) (y := y)) L

private def nativeIso : codes (old H) ≅ codes (realized H) :=
  Iso.refl _

/-- The transported family keeps the original native collapse, time diagram and raw target
while its decorated labels are the chosen prism realizations. -/
def family : Family Q (realized H) (p H ⋙ time) :=
  JTParametrizedTargetRelabel.relabel (F.precomp (p H))
    (comparison W (b (W := W) (x := x) (y := y)) L H t) (nativeIso H)
    (fun _ ↦ rfl)

end

end DaggerModels.PartII.JTOrderedLabelPaddingPrismTarget
