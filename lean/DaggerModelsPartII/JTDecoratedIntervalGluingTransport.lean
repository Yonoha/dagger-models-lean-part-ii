import DaggerModelsPartII.JTDecoratedIntervalTransport
import DaggerModelsPartII.JTDecoratedIntervalSourceRestriction

/-! The endpoint-fixed lift of compatible intervals is natural under decoration. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalGluingTransport

open NecklaceCode JTTargetJointMarks
open JTDecoratedIntervalEndpoint
open JTDecoratedIntervalTransport
open JTDecoratedIntervalMapping (leftToOverlap rightToOverlap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (K : SimplexCategory ⥤ SSet.{0})


private theorem transport_lift {C : Type*} [Category C]
    {X L R M X' L' R' M' : C}
    {p : X ⟶ L} {q : X ⟶ R} {l : L ⟶ M} {r : R ⟶ M}
    {p' : X' ⟶ L'} {q' : X' ⟶ R'} {l' : L' ⟶ M'} {r' : R' ⟶ M'}
    (sq : IsPullback p q l r) (sq' : IsPullback p' q' l' r')
    (u : X ⟶ X') (uL : L ⟶ L') (uR : R ⟶ R')
    (huL : p ≫ uL = u ≫ p') (huR : q ≫ uR = u ≫ q')
    {Z : C} (f : Z ⟶ L) (g : Z ⟶ R) (h : f ≫ l = g ≫ r) :
    ∃ h' : (f ≫ uL) ≫ l' = (g ≫ uR) ≫ r',
      sq.lift f g h ≫ u = sq'.lift (f ≫ uL) (g ≫ uR) h' := by
  let t := sq.lift f g h ≫ u
  have hL : t ≫ p' = f ≫ uL := by
    dsimp only [t]
    rw [Category.assoc, ← huL, ← Category.assoc, sq.lift_fst]
  have hR : t ≫ q' = g ≫ uR := by
    dsimp only [t]
    rw [Category.assoc, ← huR, ← Category.assoc, sq.lift_snd]
  have hh : (f ≫ uL) ≫ l' = (g ≫ uR) ≫ r' := calc
    _ = (t ≫ p') ≫ l' := congrArg (· ≫ l') hL.symm
    _ = t ≫ p' ≫ l' := Category.assoc _ _ _
    _ = t ≫ q' ≫ r' := congrArg (t ≫ ·) sq'.w
    _ = (t ≫ q') ≫ r' := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ r') hR
  refine ⟨hh, sq'.hom_ext ?_ ?_⟩
  · exact hL.trans (sq'.lift_fst _ _ _).symm
  · exact hR.trans (sq'.lift_snd _ _ _).symm

variable (P : Over Q.code) (j : Joint Q.code)
variable {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i')

/-- The glued endpoint-fixed lift transports to the lift of the transported sides.
The transported sides agree on the entire overlap. -/
theorem glue_postcomp {Z : SSet.{0}}
    (f : Z ⟶ (leftFixed W x y Q K P j i).toSSet)
    (g : Z ⟶ (rightFixed W x y Q K P j i).toSSet)
    (h : f ≫ ((leftFixed W x y Q K P j i).ι ≫ leftToOverlap W x y Q K P j i) =
      g ≫ ((rightFixed W x y Q K P j i).ι ≫ rightToOverlap W x y Q K P j i)) :
    ∃ h' : (f ≫ mapLeft W x y Q K P j u) ≫
        ((leftFixed W x y Q K P j i').ι ≫ leftToOverlap W x y Q K P j i') =
      (g ≫ mapRight W x y Q K P j u) ≫
        ((rightFixed W x y Q K P j i').ι ≫ rightToOverlap W x y Q K P j i'),
      (JTDecoratedIntervalEndpoint.isPullback W x y Q K P j i).lift f g h ≫
          mapWhole W x y Q K P j u =
        (JTDecoratedIntervalEndpoint.isPullback W x y Q K P j i').lift
          (f ≫ mapLeft W x y Q K P j u) (g ≫ mapRight W x y Q K P j u) h' :=
  transport_lift (JTDecoratedIntervalEndpoint.isPullback W x y Q K P j i)
    (JTDecoratedIntervalEndpoint.isPullback W x y Q K P j i')
    (mapWhole W x y Q K P j u) (mapLeft W x y Q K P j u) (mapRight W x y Q K P j u)
    (restrict_left W x y Q K P j u) (restrict_right W x y Q K P j u) f g h

section SourceRestriction

open JTDecoratedIntervalSourceRestriction

variable {A A' : Over Q.code} (a : A ⟶ A')

/-- Restricting a glued lift along an original source map gives the glued restrictions.
The two restricted lifts still agree on the full overlap. -/
theorem glue_precomp {Z : SSet.{0}}
    (f : Z ⟶ (leftFixed W x y Q K A' j i).toSSet)
    (g : Z ⟶ (rightFixed W x y Q K A' j i).toSSet)
    (h : f ≫ ((leftFixed W x y Q K A' j i).ι ≫ leftToOverlap W x y Q K A' j i) =
      g ≫ ((rightFixed W x y Q K A' j i).ι ≫ rightToOverlap W x y Q K A' j i)) :
    ∃ h' : (f ≫ restrictLeft W x y Q K a j i) ≫
        ((leftFixed W x y Q K A j i).ι ≫ leftToOverlap W x y Q K A j i) =
      (g ≫ restrictRight W x y Q K a j i) ≫
        ((rightFixed W x y Q K A j i).ι ≫ rightToOverlap W x y Q K A j i),
      (JTDecoratedIntervalEndpoint.isPullback W x y Q K A' j i).lift f g h ≫
          restrictWhole W x y Q K a j i =
        (JTDecoratedIntervalEndpoint.isPullback W x y Q K A j i).lift
          (f ≫ restrictLeft W x y Q K a j i) (g ≫ restrictRight W x y Q K a j i) h' :=
  transport_lift (JTDecoratedIntervalEndpoint.isPullback W x y Q K A' j i)
    (JTDecoratedIntervalEndpoint.isPullback W x y Q K A j i)
    (restrictWhole W x y Q K a j i) (restrictLeft W x y Q K a j i)
    (restrictRight W x y Q K a j i) (left_square W x y Q K a j i)
    (right_square W x y Q K a j i) f g h

end SourceRestriction

end
end DaggerModels.PartII.JTDecoratedIntervalGluingTransport
