import DaggerModelsPartII.JTActualJointCutPrism
import DaggerModelsPartII.JTJointPaddedOverlapEvaluation
import OriginalNecklaceCutMaps

/-! The literal original timed prism between two source cuts over the same target joint. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointGapPrism

open JTParametrizedTargetFamilies (Family codes)
open ReversalDiscreteFreeColimits
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)
open JTActualJointCutPrism (originalCoefficient vertexRow original_raw)
open JTComposedPrismLabels (rawProduct rawProduct_horizontal)
open TwoBeadEndpointLabel (jointLabelFromRow)
open JTTargetJointMarks (Joint)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev D := discreteFree.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (D.map f) W

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A)
private abbrev T := (codes L).obj a
private abbrev k := (JTJointRelativeGraphFamily.coefficient (L := L)).obj a
private abbrev I := J.obj (time.obj a)
variable (v w : Fin ((T (L := L) a).len + 1)) (h : v ≤ w)

/-- Keep the entire native interval between the cuts. -/
abbrev code := intervalCode (T (L := L) a) v w h

/-- Its coefficient is the genuine restriction of the old label, at the old degree. -/
def coefficient : std.obj (k (L := L) a) ⟶ labels W (code a v w h) :=
  originalCoefficient (L := L) a ≫ pre W (intervalι (T (L := L) a) v w h)

/-- Restrict the old parameter to the entire interval and the entire original time. -/
def parameter : (code a v w h).toSSet ⊗ I (time := time) a ⟶ J.obj (k (L := L) a) :=
  (intervalι (T (L := L) a) v w h ⊗ₘ 𝟙 (I a)) ≫ F.parameter a

/-- The first endpoint has the complete row coefficient of the first cut. -/
theorem coefficient_first :
    coefficient (L := L) a v w h ≫ firstRestriction W (code a v w h) =
      vertexRow (L := L) a v ≫ jointLabelFromRow W := by
  rw [coefficient, firstRestriction, Category.assoc, ← diagramMappingPrecomp_comp,
    ← D.map_comp, DaggerOriginalProductGadget.intervalPoint_first]
  simp only [vertexRow, JTActualSourceJointSupport.oldVertexRow, jointLabelFromRow,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The last endpoint has the complete row coefficient of the second cut. -/
theorem coefficient_last :
    coefficient (L := L) a v w h ≫ lastRestriction W (code a v w h) =
      vertexRow (L := L) a w ≫ jointLabelFromRow W := by
  rw [coefficient, lastRestriction, Category.assoc, ← diagramMappingPrecomp_comp,
    ← D.map_comp, DaggerOriginalProductGadget.intervalPoint_last]
  simp only [vertexRow, JTActualSourceJointSupport.oldVertexRow, jointLabelFromRow,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Pullback to the first endpoint keeps its full timed map in the old degree. -/
theorem parameter_first :
    (pointAt (code a v w h) (ULift.up 0) ⊗ₘ 𝟙 (I (time := time) a)) ≫ parameter F a v w h =
      JTActualSourceJointSupport.timeParameter F a v := by
  unfold parameter JTActualSourceJointSupport.timeParameter
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    DaggerOriginalProductGadget.intervalPoint_first]

/-- Pullback to the other endpoint keeps its full timed map in the old degree. -/
theorem parameter_last :
    (pointAt (code a v w h) (ULift.up (Fin.last (code a v w h).len)) ⊗ₘ
      𝟙 (I (time := time) a)) ≫ parameter F a v w h =
      JTActualSourceJointSupport.timeParameter F a w := by
  unfold parameter JTActualSourceJointSupport.timeParameter
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    DaggerOriginalProductGadget.intervalPoint_last]

variable (j : Joint Q.code)
variable (hv : orderMap (F.collapse.app a).map v = j.val)
variable (hw : orderMap (F.collapse.app a).map w = j.val)

private abbrev atJoint := pointAt Q.code (ULift.up j.val)

private theorem diagonalInclusion :
    intervalι.{0} Q.code j.val j.val le_rfl =
      term (intervalCode Q.code j.val j.val le_rfl).toSSet ≫ atJoint j := by
  let U := intervalCode Q.code j.val j.val le_rfl
  have hU : IsTerminal (U.toSSet : SSet.{0}) := by
    let e : (U.toSSet : SSet.{0}) ≅ point.toSSet :=
      eqToIso (congrArg (fun C : NecklaceCode ↦ NecklaceCode.toSSet.{0} C)
        (intervalCode_diagonal Q.code j.val))
    exact JTOrderedLabelJointInsertion.pointIsTerminal.ofIso e.symm
  let p := pointAt U (ULift.up 0)
  have he : term U.toSSet ≫ p = 𝟙 _ := hU.hom_ext _ _
  calc
    _ = (term U.toSSet ≫ p) ≫ intervalι Q.code j.val j.val le_rfl := by
      rw [he, Category.id_comp]
    _ = _ := by
      rw [Category.assoc]
      exact congrArg (fun f ↦ term U.toSSet ≫ f)
        (DaggerOriginalProductGadget.intervalPoint_first Q.code j.val j.val le_rfl)

include hv hw in
/-- Every simplex of the interval maps to the literal target joint. -/
theorem native_constant :
    intervalι (T (L := L) a) v w h ≫ (F.collapse.app a).map =
      term (code a v w h).toSSet ≫ atJoint j := by
  let f := (F.collapse.app a).map
  let m := DaggerOriginalProductGadget.necklaceIntervalMap f v w h j.val j.val le_rfl hv.ge hw.le
  calc
    _ = m ≫ intervalι Q.code j.val j.val le_rfl :=
      (DaggerOriginalProductGadget.necklaceIntervalMap_fac f v w h
        j.val j.val le_rfl hv.ge hw.le).symm
    _ = _ := by
      rw [diagonalInclusion j, ← Category.assoc]
      exact congrArg (fun f ↦ f ≫ atJoint j) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

include hv hw in
theorem raw_constant :
    rawProduct W (parameter F a v w h) (coefficient (L := L) a v w h) =
      fst (code a v w h).toSSet (I (time := time) a) ≫ term (code a v w h).toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W (jointCoefficient (Q := Q) j)) := by
  let u := intervalι.{0} (T (L := L) a) v w h
  rw [parameter, coefficient, ← rawProduct_horizontal]
  calc
    _ = (u ⊗ₘ 𝟙 (I a)) ≫
        fst (T (L := L) a).toSSet (I a) ≫ (F.collapse.app a).map ≫ Q.map :=
      congrArg (fun g ↦ (u ⊗ₘ 𝟙 (I a)) ≫ g) (original_raw F a)
    _ = _ := by
      rw [tensorHom_fst_assoc, ← Category.assoc u, native_constant F a v w h j hv hw]
      simp only [Category.assoc]
      exact congrArg
        (fun g ↦ fst (code a v w h).toSSet (I a) ≫ term (code a v w h).toSSet ≫ g)
        (JTJointPaddedOverlapEvaluation.target_map (Q := Q) j).symm

end
end DaggerModels.PartII.JTActualJointGapPrism
