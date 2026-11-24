import DaggerModelsPartII.JTActualSourceJointSupport
import DaggerModelsPartII.JTComposedPrismLabels
import OriginalProductCrossingEndpoints

/-! The literal cut coefficients and the exact supported row at their common endpoint. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointCutPrism

open ReversalDiscreteFreeColimits OrderedNecklaceVertexPoints
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)
open JTParametrizedTargetFamilies (Family codes)
open DaggerOriginalProductGadget (cutLeft_joint cutRight_joint)
open JTProjectiveOrderedFiberComparison (row)
open TwoBeadEndpointLabel (jointLabelFromRow)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter
private abbrev D := discreteFree.{0}

private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (D.map i) W

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A] {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A)

private abbrev T := (codes L).obj a
private abbrev k := (JTJointRelativeGraphFamily.coefficient (L := L)).obj a
private abbrev I := J.obj (time.obj a)

/-- The whole original coefficient in its native mapping space. -/
abbrev originalCoefficient : std.obj (k (L := L) a) ⟶ labels W (T (L := L) a) :=
  JTActualSourceJointSupport.oldCoefficient (L := L) a

variable (v : Fin ((T (L := L) a).len + 1))
private abbrev E := T (L := L) a

/-- The restriction of the old coefficient to the actual left cut. -/
def leftCoefficient : std.obj (k (L := L) a) ⟶ labels W (cutLeft (E a) v) :=
  originalCoefficient (L := L) a ≫ pre W (cutLeftι (E a) v)

/-- The restriction of the old coefficient to the actual right cut. -/
def rightCoefficient : std.obj (k (L := L) a) ⟶ labels W (cutRight (E a) v) :=
  originalCoefficient (L := L) a ≫ pre W (cutRightι (E a) v)

/-- The original parameter on the entire left cut and all time simplices. -/
def leftParameter : (cutLeft (E a) v).toSSet ⊗ I (time := time) a ⟶ J.obj (k (L := L) a) :=
  (cutLeftι (E a) v ⊗ₘ 𝟙 (I a)) ≫ F.parameter a

/-- The original parameter on the entire right cut and all time simplices. -/
def rightParameter : (cutRight (E a) v).toSSet ⊗ I (time := time) a ⟶ J.obj (k (L := L) a) :=
  (cutRightι (E a) v ⊗ₘ 𝟙 (I a)) ≫ F.parameter a

private abbrev chosenVertex := pointAt (E a) (ULift.up v)

/-- The common coefficient at the cut, in the original zero row. -/
abbrev vertexRow : std.obj (k (L := L) a) ⟶ row W ⦋0⦌ :=
  JTActualSourceJointSupport.oldVertexRow (L := L) a v

private theorem vertexRow_mapping :
    vertexRow (L := L) a v ≫ jointLabelFromRow W =
      originalCoefficient (L := L) a ≫ pre W (chosenVertex a v) := by
  simp only [vertexRow, JTActualSourceJointSupport.oldVertexRow, jointLabelFromRow,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inner endpoint of the left cut has the chosen full row. -/
theorem left_last :
    leftCoefficient (L := L) a v ≫ lastRestriction W (cutLeft (E a) v) =
      vertexRow (L := L) a v ≫ jointLabelFromRow W := by
  rw [vertexRow_mapping, leftCoefficient, lastRestriction, Category.assoc,
    ← diagramMappingPrecomp_comp, ← D.map_comp, cutLeft_joint]

/-- The inner endpoint of the right cut has the same full row. -/
theorem right_first :
    rightCoefficient (L := L) a v ≫ firstRestriction W (cutRight (E a) v) =
      vertexRow (L := L) a v ≫ jointLabelFromRow W := by
  rw [vertexRow_mapping, rightCoefficient, firstRestriction, Category.assoc,
    ← diagramMappingPrecomp_comp, ← D.map_comp, cutRight_joint]

/-- The left cut retains all coefficients of the original outer endpoint. -/
theorem left_first :
    leftCoefficient (L := L) a v ≫ firstRestriction W (cutLeft (E a) v) =
      term (std.obj (k (L := L) a)) ≫ zeroPoint W x := by
  rw [leftCoefficient, firstRestriction, Category.assoc,
    ← diagramMappingPrecomp_comp, ← D.map_comp]
  change originalCoefficient (L := L) a ≫ pre W
    (pointAt (cutLeft (E a) v) (ULift.up 0) ≫ cutLeftι (E a) v) = _
  have h : pointAt (cutLeft (E a) v) (ULift.up 0) ≫ cutLeftι (E a) v =
      pointAt (E a) (ULift.up 0) :=
    DaggerOriginalProductGadget.intervalPoint_first (E a) 0 v (Fin.zero_le v)
  rw [h]
  exact JTOrderedLabelBinaryGlue.coefficient_first _ _ _ _ _ _

/-- The right cut retains all coefficients of the other original outer endpoint. -/
theorem right_last :
    rightCoefficient (L := L) a v ≫ lastRestriction W (cutRight (E a) v) =
      term (std.obj (k (L := L) a)) ≫ zeroPoint W y := by
  rw [rightCoefficient, lastRestriction, Category.assoc,
    ← diagramMappingPrecomp_comp, ← D.map_comp]
  change originalCoefficient (L := L) a ≫ pre W
    (pointAt (cutRight (E a) v) (ULift.up (Fin.last _)) ≫ cutRightι (E a) v) = _
  have h : pointAt (cutRight (E a) v) (ULift.up (Fin.last _)) ≫ cutRightι (E a) v =
      pointAt (E a) (ULift.up (Fin.last (E a).len)) :=
    DaggerOriginalProductGadget.intervalPoint_last (E a) v (Fin.last (E a).len) (Fin.le_last v)
  rw [h]
  exact JTOrderedLabelBinaryGlue.coefficient_last _ _ _ _ _ _

/-- The exact original raw equality before the two ordered endpoints are imposed. -/
theorem original_raw :
    JTComposedPrismLabels.rawProduct W (F.parameter a) (originalCoefficient (L := L) a) =
      fst (E a).toSSet (I (time := time) a) ≫ (F.collapse.app a).map ≫ Q.map := by
  unfold originalCoefficient JTActualSourceJointSupport.oldCoefficient
    JTOrderedLabelBinaryGlue.coefficient
  dsimp only [JTComposedPrismLabels.rawProduct]
  erw [Equiv.apply_symm_apply]
  exact JTParametrizedTargetFamilies.rawProduct F a

/-- On the full left prism, the old coefficient still realizes to the literal original map. -/
theorem left_raw :
    JTComposedPrismLabels.rawProduct W (leftParameter F a v) (leftCoefficient (L := L) a v) =
      fst (cutLeft (E a) v).toSSet (I (time := time) a) ≫
        cutLeftι (E a) v ≫ (F.collapse.app a).map ≫ Q.map := by
  rw [leftParameter, leftCoefficient, ← JTComposedPrismLabels.rawProduct_horizontal]
  calc
    _ = (cutLeftι (E a) v ⊗ₘ 𝟙 (I a)) ≫
        fst (E a).toSSet (I a) ≫ (F.collapse.app a).map ≫ Q.map :=
      congrArg (fun g ↦ (cutLeftι (E a) v ⊗ₘ 𝟙 (I a)) ≫ g) (original_raw F a)
    _ = _ := by simp only [tensorHom_fst_assoc]

/-- On the full right prism, the old coefficient still realizes to the literal original map. -/
theorem right_raw :
    JTComposedPrismLabels.rawProduct W (rightParameter F a v) (rightCoefficient (L := L) a v) =
      fst (cutRight (E a) v).toSSet (I (time := time) a) ≫
        cutRightι (E a) v ≫ (F.collapse.app a).map ≫ Q.map := by
  rw [rightParameter, rightCoefficient, ← JTComposedPrismLabels.rawProduct_horizontal]
  calc
    _ = (cutRightι (E a) v ⊗ₘ 𝟙 (I a)) ≫
        fst (E a).toSSet (I a) ≫ (F.collapse.app a).map ≫ Q.map :=
      congrArg (fun g ↦ (cutRightι (E a) v ⊗ₘ 𝟙 (I a)) ≫ g) (original_raw F a)
    _ = _ := by simp only [tensorHom_fst_assoc]

end
end DaggerModels.PartII.JTActualJointCutPrism
