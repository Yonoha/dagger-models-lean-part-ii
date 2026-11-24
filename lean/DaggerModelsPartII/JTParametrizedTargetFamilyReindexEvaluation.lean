import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTBoundaryNecklacePresentationTransport

/-! Reindexing the full evaluation of a parametrized target family. -/

set_option autoImplicit false
set_option maxHeartbeats 300000

open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetFamilies

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A B : Type} [SmallCategory A] [SmallCategory B]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory}

/-- Reindex the presentation retaining the exact internal necklace and its map. -/
abbrev reindexPresentation (G : B ⥤ A) :
    Presentation (L := G ⋙ L) (time := G ⋙ time) ⥤ Presentation (L := L) (time := time) :=
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram (cylinders (L := L) (time := time))) G

private abbrev E := JTTargetCommaPullback.diagram W x y Q
private abbrev X := cylinders (L := L) (time := time)

private def reindexLift (F : Family Q L time) (G : B ⥤ A) :
    G ⋙ X (L := L) (time := time) ⟶ (G ⋙ L) ⋙ E (Q := Q) :=
  liftNatural (Q := Q) (L := G ⋙ L) (time := G ⋙ time)
    (Family.precomp (Q := Q) (L := L) (time := time) F G)

private theorem reindexLift_square (F : Family Q L time) (G : B ⥤ A) (i : B) :
    (reindexLift F G).app i ≫ (E (Q := Q)).map (NatTrans.app (𝟙 (G ⋙ L)) i) =
      (liftNatural (Q := Q) (L := L) (time := time) F).app (G.obj i) := by
  rw [NatTrans.id_app, (E (Q := Q)).map_id]
  exact Category.comp_id _

/-- Each reindexed graph compares to the original evaluation at the same objects and operators. -/
def compareEvaluation_precomp (F : Family Q L time) (G : B ⥤ A) :=
  Functor.whiskerRight
    (JTBoundaryNecklacePresentationTransport.comparisonWhisker (E (Q := Q)) (X (L := L) (time := time))
      (liftNatural (Q := Q) (L := L) (time := time) F) G
      (reindexLift F G) (𝟙 (G ⋙ L)) (reindexLift_square F G))
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

private def associateTarget {U V X Y : Type}
    [SmallCategory U] [SmallCategory V] [SmallCategory X] [SmallCategory Y]
    {H : U ⥤ Y} {a : U ⥤ V} {b : V ⥤ X} {c : X ⥤ Y}
    (h : H ⟶ (a ⋙ b) ⋙ c) : H ⟶ a ⋙ (b ⋙ c) :=
  h ≫ eqToHom (Functor.assoc a b c)

private def associatedReindex (F : Family Q L time) (G : B ⥤ A) :=
  associateTarget (compareEvaluation_precomp F G)

/-- Compare the reindexed evaluation with the original evaluation on every
internal necklace and arrow, with the reindexing functor as a single factor. -/
def compareEvaluation_reindex (F : Family Q L time) (G : B ⥤ A) :
    evaluate (F.precomp G) ⟶
      reindexPresentation (L := L) (time := time) G ⋙ evaluate F :=
  associatedReindex F G

end
end DaggerModels.PartII.JTParametrizedTargetFamilies
