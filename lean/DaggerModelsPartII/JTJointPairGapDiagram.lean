import DaggerModelsPartII.JTJointPairSourceDiagram
import DaggerModelsPartII.JTActualJointGapPrism
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import OriginalNecklaceCutMaps

/-! The whole original interval and its timed coefficient over ordered pairs of cuts. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerModels.PartII.ReversalDiscreteFreeColimits

namespace DaggerModels.PartII.JTJointPairGapDiagram

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.{0}.map f) W

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointPairSourceDiagram.Index F j
private abbrev base := JTJointPairSourceDiagram.base F j
private abbrev T (p : I F j) := (codes L).obj ((base F j).obj p)
private abbrev v (p : I F j) := p.2.left.val
private abbrev w (p : I F j) := p.2.right.val
private abbrev h (p : I F j) := p.2.le

/-- The original interval between the two cuts, without collapsing its coefficient. -/
abbrev code (p : I F j) := intervalCode (T F j p) (v F j p) (w F j p) (h F j p)

/-- The actual inclusion of the whole interval into the old native necklace. -/
abbrev inclusion (p : I F j) : (code F j p).toSSet ⟶ (T F j p).toSSet :=
  intervalι (T F j p) (v F j p) (w F j p) (h F j p)

/-- Exact interval transport induced by one original source arrow. -/
def codeMap {p q : I F j} (f : p ⟶ q) : code F j p ⟶ code F j q :=
  DaggerOriginalProductGadget.intervalCodeHom ((codes L).map f.val).map
    (v F j p) (w F j p) (h F j p)
    (v F j q) (w F j q) (h F j q)
    (JTJointPairSourceDiagram.left_map F j f)
    (JTJointPairSourceDiagram.right_map F j f)

/-- The interval operator commutes with both literal inclusions. -/
theorem codeMap_fac {p q : I F j} (f : p ⟶ q) :
    (codeMap F j f).map ≫ inclusion F j q =
      inclusion F j p ≫ ((codes L).map f.val).map :=
  DaggerOriginalProductGadget.necklaceIntervalMap_fac
    ((codes L).map f.val).map (v F j p) (w F j p) (h F j p)
    (v F j q) (w F j q) (h F j q)
    (JTJointPairSourceDiagram.left_map F j f).ge
    (JTJointPairSourceDiagram.right_map F j f).le

/-- Every original arrow transports the entire interval, including both endpoints. -/
def native : I F j ⥤ NecklaceCode where
  obj := code F j
  map := codeMap F j
  map_id p := by
    apply NecklaceCode.Hom.ext
    haveI : Mono (inclusion F j p) := inferInstance
    apply (cancel_mono (inclusion F j p)).mp
    rw [codeMap_fac]
    change inclusion F j p ≫ ((codes L).map (𝟙 p.1)).map =
      (NecklaceCode.Hom.id (code F j p)).map ≫ inclusion F j p
    rw [(codes L).map_id]
    change inclusion F j p ≫ 𝟙 _ = 𝟙 _ ≫ inclusion F j p
    simp
  map_comp {p q r} f g := by
    apply NecklaceCode.Hom.ext
    haveI : Mono (inclusion F j r) := inferInstance
    apply (cancel_mono (inclusion F j r)).mp
    change (codeMap F j (f ≫ g)).map ≫ inclusion F j r =
      ((codeMap F j f).map ≫ (codeMap F j g).map) ≫ inclusion F j r
    rw [codeMap_fac, Category.assoc, codeMap_fac, ← Category.assoc, codeMap_fac]
    change inclusion F j p ≫ ((codes L).map (f.val ≫ g.val)).map =
      inclusion F j p ≫ ((codes L).map f.val).map ≫ ((codes L).map g.val).map
    rw [(codes L).map_comp]
    rfl

/-- The native interval inclusions are natural in every pair-preserving arrow. -/
def inclusions : native F j ⋙ NecklaceCode.simplicialFunctor ⟶
    base F j ⋙ codes L ⋙ NecklaceCode.simplicialFunctor where
  app := inclusion F j
  naturality _ _ f := codeMap_fac F j f

private abbrev degree := JTJointRelativeGraphFamily.coefficient (L := L)

/-- The full old coefficient, restricted only in the native interval direction. -/
abbrev coefficient (p : I F j) :=
  JTActualJointGapPrism.coefficient (L := L) ((base F j).obj p)
    (v F j p) (w F j p) (h F j p)

/-- The complete old time parameter on the whole interval. -/
abbrev parameter (p : I F j) :=
  JTActualJointGapPrism.parameter F ((base F j).obj p)
    (v F j p) (w F j p) (h F j p)

/-- The old interval coefficient retains the complete original degree and its exact operator. -/
theorem coefficient_map {p q : I F j} (f : p ⟶ q) :
    coefficient F j p =
      std.map ((degree (L := L)).map f.val) ≫ coefficient F j q ≫
        pre W (codeMap F j f).map := by
  let B := OrderedNecklaceVertexPoints.boundaryPoint W x y
  let P := OrderedLabelElements.projection W B
  have hold := JTOrderedLabelWedge.coefficient_of_indexHom
    (W := W) (x := x) (y := y)
    (OrderedLabelElements.label W B (L.obj p.1))
    (OrderedLabelElements.label W B (L.obj q.1))
    ((codes L).map f.val) ((degree (L := L)).map f.val) (L.map f.val)
    (show P.map (L.map f.val) =
      ((codes L).map f.val, (degree (L := L)).map f.val) from rfl)
  have hold' : JTActualJointCutPrism.originalCoefficient (L := L) p.1 =
      std.map ((degree (L := L)).map f.val) ≫
        JTActualJointCutPrism.originalCoefficient (L := L) q.1 ≫
          pre W ((codes L).map f.val).map := by
    simpa only [JTActualJointCutPrism.originalCoefficient,
      JTActualSourceJointSupport.oldCoefficient] using hold
  change JTActualJointCutPrism.originalCoefficient (L := L) p.1 ≫
      pre W (inclusion F j p) =
    std.map ((degree (L := L)).map f.val) ≫
      (JTActualJointCutPrism.originalCoefficient (L := L) q.1 ≫
        pre W (inclusion F j q)) ≫ pre W (codeMap F j f).map
  rw [hold']
  simp only [Category.assoc, ← diagramMappingPrecomp_comp,
    ← discreteFree.map_comp, codeMap_fac]

/-- The original time and coefficient operators commute on the entire gap prism. -/
theorem parameter_map {p q : I F j} (f : p ⟶ q) :
    ((codeMap F j f).map ⊗ₘ J.map (time.map f.val)) ≫ parameter F j q =
      parameter F j p ≫ J.map ((degree (L := L)).map f.val) := by
  unfold parameter JTActualJointGapPrism.parameter
  rw [← Category.assoc, tensorHom_comp_tensorHom, codeMap_fac,
    Category.assoc, ← tensorHom_comp_tensorHom, ← Category.assoc]
  exact congrArg (fun u ↦ (inclusion F j p ⊗ₘ 𝟙 (J.obj (time.obj p.1))) ≫ u)
    (F.parameter_map f.val)

/-- Raw evaluation of the whole interval is the genuine joint point. -/
theorem raw_constant (p : I F j) :
    JTComposedPrismLabels.rawProduct W (parameter F j p) (coefficient F j p) =
      fst (code F j p).toSSet (J.obj (time.obj p.1)) ≫
        SSet.stdSimplex.isTerminalObj₀.from (code F j p).toSSet ≫
          SSet.yonedaEquiv.symm (rawVertex W
            (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) :=
  JTActualJointGapPrism.raw_constant F p.1 (v F j p) (w F j p) (h F j p)
    j p.2.left.property p.2.right.property

end
end DaggerModels.PartII.JTJointPairGapDiagram
