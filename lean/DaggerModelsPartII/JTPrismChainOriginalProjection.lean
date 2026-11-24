import DaggerModelsPartII.JTOrderedLabelPaddingPrismChainCylinder
import DaggerModelsPartII.JTParametrizedTargetFamilyReindexEvaluation

/-! Project the full chain comparison back to the original evaluation. -/

set_option autoImplicit false
set_option maxHeartbeats 300000

open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTPrismChainOriginalProjection

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family)
open BoundaryNecklaceComma (fiberDiagram)
open JTOrderedLabelPaddingPrismChainCylinder
  (reduced commonEvaluation compareOriginal presentationProjection)

noncomputable section

private def normalizeComparison {K : Type} [SmallCategory K] {D : K ⥤ Cat.{0, 0}}
    {I J C : Type} [SmallCategory I] [SmallCategory J] [SmallCategory C]
    {l : Grothendieck D ⥤ J} {u : Grothendieck D ⥤ I}
    {v : J ⥤ I} {H : I ⥤ C}
    (h : (Grothendieck.pre D (𝟭 K) ⋙ u) ⋙ H ⟶ (l ⋙ v) ⋙ H) :
    u ⋙ H ⟶ l ⋙ (v ⋙ H) :=
  eqToHom (congrArg (· ⋙ H)
    ((congrArg (· ⋙ u) (Grothendieck.pre_id (F := D))).trans (Functor.id_comp u))).symm ≫
      h ≫ eqToHom (Functor.assoc l v H)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time)

/-- The comparison to the old evaluation with its identity reindexing removed. -/
private def normalizeCompareOriginal := normalizeComparison (compareOriginal F)


open JTParametrizedTargetFamilies (evaluate reindexPresentation)

private abbrev b := boundaryPoint W x y
private abbrev chainBase :=
  JTOrderedLabelPaddingPrismChains.base W (b (W := W) (x := x) (y := y)) L ⋙
    JTOrderedLabelPaddingPrismSliceArrow.originalBase W (b (W := W) (x := x) (y := y)) L

/-- Forget the chain by projecting all internal necklaces to the original cylinder. -/
abbrev projectToOriginal :=
  presentationProjection F ⋙ reindexPresentation (L := L) (time := time) (chainBase (L := L))

private def compareAtOldIndex : commonEvaluation F ⟶
    presentationProjection F ⋙ evaluate (F.precomp (chainBase (L := L))) :=
  normalizeCompareOriginal F

private def pasteComparison {U V X Y : Type} [SmallCategory U] [SmallCategory V]
    [SmallCategory X] [SmallCategory Y]
    {a : U ⥤ Y} {l : U ⥤ V} {b : V ⥤ Y} {f : V ⥤ X} {c : X ⥤ Y}
    (h : a ⟶ l ⋙ b) (k : b ⟶ f ⋙ c) : a ⟶ (l ⋙ f) ⋙ c :=
  h ≫ Functor.whiskerLeft l k ≫ eqToHom (Functor.assoc l f c).symm

def compareProjectedOriginal :
    commonEvaluation F ⟶ projectToOriginal F ⋙ evaluate F :=
  pasteComparison (compareAtOldIndex F)
    (JTParametrizedTargetFamilies.compareEvaluation_reindex F (chainBase (L := L)))

theorem projectToOriginal_base :
    projectToOriginal F ⋙
      Grothendieck.forget (fiberDiagram
        (JTParametrizedTargetFamilies.cylinders (L := L) (time := time))) =
      Grothendieck.forget (fiberDiagram (reduced F)) ⋙ chainBase (L := L) := rfl

end
end DaggerModels.PartII.JTPrismChainOriginalProjection
