import DaggerModelsPartII.JTPrismChainOriginalProjection
import DaggerModelsPartII.JTParametrizedTargetFamilyReindexEvaluation

/-! Reindex the projected chain comparison before applying a global tail map. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismChainCylinder

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family cylinders evaluate reindexPresentation)
open BoundaryNecklaceComma (fiberDiagram)
open JTGraphFactoredPresentation (TargetComma)
open JTPrismChainOriginalProjection
  (projectToOriginal projectToOriginal_base compareProjectedOriginal)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A K : Type} [SmallCategory A] [SmallCategory K] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (G : K ⥤ A)

private abbrev base (F : K ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)) :=
  JTOrderedLabelPaddingPrismChains.base W (boundaryPoint W x y) F ⋙
    JTOrderedLabelPaddingPrismSliceArrow.originalBase W (boundaryPoint W x y) F

private abbrev forgetFamily :=
  Grothendieck.forget (fiberDiagram (cylinders (L := L) (time := time)))

private def projectToGlobal :=
  projectToOriginal (F.precomp G) ⋙ reindexPresentation (L := L) (time := time) G

private theorem pre_forget {A K : Type} [SmallCategory A] [SmallCategory K]
    (D : A ⥤ Cat.{0, 0}) (G : K ⥤ A) :
    Grothendieck.pre D G ⋙ Grothendieck.forget D =
      Grothendieck.forget (G ⋙ D) ⋙ G := rfl

private theorem projectToGlobal_base :
    projectToGlobal F G ⋙ forgetFamily (L := L) (time := time) =
      (Grothendieck.forget (fiberDiagram (reduced (F.precomp G))) ⋙ base (G ⋙ L)) ⋙ G := by
  let C := projectToOriginal (F.precomp G)
  let D := fiberDiagram (cylinders (L := L) (time := time))
  let P := reindexPresentation (L := L) (time := time) G
  let U := Grothendieck.forget (G ⋙ D)
  let V := forgetFamily (L := L) (time := time)
  change (C ⋙ P) ⋙ V = _
  calc
    _ = C ⋙ (P ⋙ V) := Functor.assoc C P V
    _ = C ⋙ (U ⋙ G) := congrArg (C ⋙ ·) (pre_forget D G)
    _ = (C ⋙ U) ⋙ G := (Functor.assoc C U G).symm
    _ = _ := congrArg (· ⋙ G) (projectToOriginal_base (F.precomp G))

private def pasteComparison {U V X Y : Type} [SmallCategory U] [SmallCategory V]
    [SmallCategory X] [SmallCategory Y]
    {a : U ⥤ Y} {l : U ⥤ V} {b : V ⥤ Y} {f : V ⥤ X} {c : X ⥤ Y}
    (h : a ⟶ l ⋙ b) (k : b ⟶ f ⋙ c) : a ⟶ (l ⋙ f) ⋙ c :=
  h ≫ Functor.whiskerLeft l k ≫ eqToHom (Functor.assoc l f c).symm

set_option maxHeartbeats 650000 in
private def compareToGlobal :
    commonEvaluation (F.precomp G) ⟶ projectToGlobal F G ⋙ evaluate F := by
  let h : evaluate (F.precomp G) ⟶
      reindexPresentation (L := L) (time := time) G ⋙ evaluate F :=
    JTParametrizedTargetFamilies.compareEvaluation_reindex F G
  exact pasteComparison (compareProjectedOriginal (F.precomp G)) h

private def pasteToTail {B C K S : Type} [SmallCategory B] [SmallCategory C]
    [SmallCategory K] [SmallCategory S]
    {f : B ⥤ C} {p : B ⥤ S} {g : S ⥤ C} {q : S ⥤ K} {t : K ⥤ C}
    {b : B ⥤ K}
    (h : f ⟶ p ⋙ g) (k : g ⟶ q ⋙ t) (e : p ⋙ q = b) : f ⟶ b ⋙ t :=
  h ≫ Functor.whiskerLeft p k ≫
    eqToHom ((Functor.assoc p q t).symm.trans (congrArg (· ⋙ t) e))

/-- A global tail comparison induces the original tail comparison after
projecting the whole chain presentation of a reindexed family. -/
def compareReindexedToTail (tail : A ⥤ TargetComma Q)
    (h : evaluate F ⟶ forgetFamily (L := L) (time := time) ⋙ tail) :
    commonEvaluation (F.precomp G) ⟶
      ((Grothendieck.forget (fiberDiagram (reduced (F.precomp G))) ⋙ base (G ⋙ L)) ⋙ G) ⋙ tail :=
  pasteToTail (compareToGlobal F G) h (projectToGlobal_base F G)

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismChainCylinder
