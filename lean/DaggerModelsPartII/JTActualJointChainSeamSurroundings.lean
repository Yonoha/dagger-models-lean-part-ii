import DaggerModelsPartII.JTExactlyMarkedCutDiagrams
import DaggerModelsPartII.JTActualJointChainSeamChoices

/-!
The genuine two uncorrected outer cuts around an actual correction seam.
The old coefficients, global endpoints and mixed naturality derive every field
of the existing seam Surroundings structure. No surrounding-label input is added.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointChainSeamSurroundings

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map g) W

private theorem reindex_endpoint {d k : SimplexCategory} (a : d ⟶ k)
    {M X : SSet.{0}} (c : std.obj k ⟶ M) (r : M ⟶ X) (v : (Δ[0] : SSet.{0}) ⟶ X)
    (h : c ≫ r = term (std.obj k) ≫ v) :
    (std.map a ≫ c) ≫ r = term (std.obj d) ≫ v := by
  rw [Category.assoc, h, ← Category.assoc]
  congr 1

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChoiceChainGraph.Index F j
private abbrev K := JTActualJointChoiceChainGraph.ordinals F j
private abbrev marked := JTActualJointChainSeamData.marked F j
private abbrev α := JTActualJointChoiceChainGraph.toOriginal F j
private abbrev endpointRows := JTActualJointChainSeamData.endpointRows F j

/-- The actual left native cut, before inserting any correction edge. -/
abbrev leftNative : I F j ⥤ NecklaceCode :=
  marked F j ⋙ JTExactlyMarkedCutDiagrams.leftNative F j

/-- The actual right native cut at the same original source vertex. -/
abbrev rightNative : I F j ⥤ NecklaceCode :=
  marked F j ⋙ JTExactlyMarkedCutDiagrams.rightNative F j

private abbrev leftCoefficient (p : I F j) :
    std.obj ((K F j).obj p) ⟶ labels W ((leftNative F j).obj p) :=
  std.map ((α F j).app p) ≫
    JTExactlyMarkedCutDiagrams.leftCoefficient F j ((marked F j).obj p)

private abbrev rightCoefficient (p : I F j) :
    std.obj ((K F j).obj p) ⟶ labels W ((rightNative F j).obj p) :=
  std.map ((α F j).app p) ≫
    JTExactlyMarkedCutDiagrams.rightCoefficient F j ((marked F j).obj p)

private theorem rowZero_first :
    JTNativeRowLabel.labelFromRow W 0 ≫ firstRestriction W (single 0) =
      TwoBeadEndpointLabel.jointLabelFromRow W := by
  have h := JTNativeRowLabel.labelFromRow_vertex W 0 0
  have hv : JTMixedGraphEndpointLifts.rowVertex W ⦋0⦌ 0 = 𝟙 _ := by
    have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    unfold JTMixedGraphEndpointLifts.rowVertex
    rw [hc]
    exact (JTRealizationDiagonal.ordinaryCurry.obj
      (JTReversalInput.ordinaryInput.obj W)).map_id _
  simpa only [firstRestriction, hv, Category.id_comp] using h

private theorem rowZero_last :
    JTNativeRowLabel.labelFromRow W 0 ≫ lastRestriction W (single 0) =
      TwoBeadEndpointLabel.jointLabelFromRow W :=
  rowZero_first (W := W)

private theorem left_natural {p q : I F j} (g : p ⟶ q) :
    leftCoefficient F j p = std.map ((K F j).map g) ≫
      leftCoefficient F j q ≫ pre W ((leftNative F j).map g).map := by
  have h := JTExactlyMarkedCutDiagrams.left_natural F j ((marked F j).map g)
  change JTExactlyMarkedCutDiagrams.leftCoefficient F j ((marked F j).obj p) =
    std.map ((JTExactlyMarkedSourceDiagram.degrees F j).map ((marked F j).map g)) ≫
      JTExactlyMarkedCutDiagrams.leftCoefficient F j ((marked F j).obj q) ≫
        pre W ((leftNative F j).map g).map at h
  change std.map ((α F j).app p) ≫ _ = _
  rw [h]
  have hα := congrArg std.map ((α F j).naturality g)
  simpa only [Functor.comp_map, std.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫
      JTExactlyMarkedCutDiagrams.leftCoefficient F j ((marked F j).obj q) ≫
        pre W ((leftNative F j).map g).map) hα.symm

private theorem right_natural {p q : I F j} (g : p ⟶ q) :
    rightCoefficient F j p = std.map ((K F j).map g) ≫
      rightCoefficient F j q ≫ pre W ((rightNative F j).map g).map := by
  have h := JTExactlyMarkedCutDiagrams.right_natural F j ((marked F j).map g)
  change JTExactlyMarkedCutDiagrams.rightCoefficient F j ((marked F j).obj p) =
    std.map ((JTExactlyMarkedSourceDiagram.degrees F j).map ((marked F j).map g)) ≫
      JTExactlyMarkedCutDiagrams.rightCoefficient F j ((marked F j).obj q) ≫
        pre W ((rightNative F j).map g).map at h
  change std.map ((α F j).app p) ≫ _ = _
  rw [h]
  have hα := congrArg std.map ((α F j).naturality g)
  simpa only [Functor.comp_map, std.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫
      JTExactlyMarkedCutDiagrams.rightCoefficient F j ((marked F j).obj q) ≫
        pre W ((rightNative F j).map g).map) hα.symm

/-- Both genuine old outer cuts supply every seam surroundings field, with
the actual varying cut row and both unchanged global endpoints. -/
def surroundings : JTChosenSeamChainDiagram.Surroundings W (K F j)
    (endpointRows F j) (leftNative F j) (rightNative F j) x y where
  left := leftCoefficient F j
  right := rightCoefficient F j
  left_join p := by
    have h := congrArg (fun t ↦ std.map ((α F j).app p) ≫ t)
      (JTActualJointCutPrism.left_last (L := L)
        ((marked F j).obj p).1 ((marked F j).obj p).2.val)
    simpa only [Category.assoc, rowZero_first] using h
  right_join p := by
    have h := congrArg (fun t ↦ std.map ((α F j).app p) ≫ t)
      (JTActualJointCutPrism.right_first (L := L)
        ((marked F j).obj p).1 ((marked F j).obj p).2.val)
    simpa only [Category.assoc, rowZero_last] using h.symm
  first p := reindex_endpoint ((α F j).app p)
    (JTExactlyMarkedCutDiagrams.leftCoefficient F j ((marked F j).obj p))
    (firstRestriction W ((leftNative F j).obj p)) (OrderedNecklaceVertexPoints.zeroPoint W x)
    (JTActualJointCutPrism.left_first (L := L)
      ((marked F j).obj p).1 ((marked F j).obj p).2.val)
  last p := reindex_endpoint ((α F j).app p)
    (JTExactlyMarkedCutDiagrams.rightCoefficient F j ((marked F j).obj p))
    (lastRestriction W ((rightNative F j).obj p)) (OrderedNecklaceVertexPoints.zeroPoint W y)
    (JTActualJointCutPrism.right_last (L := L)
      ((marked F j).obj p).1 ((marked F j).obj p).2.val)
  left_nat g := left_natural F j g
  right_nat g := right_natural F j g

end
end DaggerModels.PartII.JTActualJointChainSeamSurroundings
