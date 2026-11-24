import DaggerModelsPartII.JTActualJointChoiceChainGraph
import DaggerModelsPartII.JTComposedPrismLabelOperators
import DaggerModelsPartII.JTActualJointCutCoefficientTransport
import DaggerModelsPartII.JTWhiskerEdgeCoefficient
import OriginalCutMapLaws

/-! Corrected left and right labels on all higher relative edge chains. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointChainSideLabels

open JTParametrizedTargetFamilies (Family codes)
open ReversalDiscreteFreeColimits
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row endpointArrow)
open JTComposedPrismLabels (Coefficients)
open OrderedNecklaceVertexPoints (zeroPoint)
open TripleBeadEndpointLabel (firstRestriction lastRestriction)
open TwoBeadEndpointLabel (edgeLabelFromRow jointLabelFromRow jointLabelFromRow_vertex)
open JTActualJointCutPrism (leftCoefficient rightCoefficient left_first left_last
  right_first right_last)
open JTJointEndpointRelativeLift (boundaryPair reverseBoundaryPair
  boundaryPair_endpoints reverseBoundaryPair_endpoints)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev E := single 1

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev C := JTActualJointChoiceChainGraph.Index F j
private abbrev b (p : C F j) := (JTActualJointChoiceChainGraph.base F j).obj p
private abbrev marked (p : C F j) := (JTActualJointChoiceCover.projection F j).obj (b F j p)
private abbrev old (p : C F j) := (marked F j p).1
private abbrev vertex (p : C F j) := (marked F j p).2.val
private abbrev n (p : C F j) := (JTActualJointChoiceChainGraph.ordinals F j).obj p
private abbrev α (p : C F j) := (JTActualJointChoiceChainGraph.toOriginal F j).app p
private abbrev β (p : C F j) := (JTActualJointChoiceChainGraph.toTime F j).app p
private abbrev z := jointCoefficient (Q := Q) j
private abbrev code (p : C F j) := (codes L).obj (old F j p)
private abbrev rowVertex (p : C F j) :=
  std.map (α F j p) ≫ JTActualJointCutPrism.vertexRow (L := L)
    (old F j p) (vertex F j p)
private abbrev ending (p : C F j) := (JTActualJointChoiceChainGraph.chainEnding F j).app p
private abbrev starting (p : C F j) := (JTActualJointChoiceChainGraph.chainStarting F j).app p

/-- The chosen ending edge has the exact old cut vertex at its first end. -/
theorem ending_pair (p : C F j) :
    ending F j p ≫ endpointArrow W = boundaryPair W (rowVertex F j p) (z j) := by
  have h := JTActualJointChoicePrism.ending_chain_endpoints F j (b F j p)
    (α F j p) (β F j p)
  exact h

/-- The starting edge has the same cut vertex at its last end. -/
theorem starting_pair (p : C F j) :
    starting F j p ≫ endpointArrow W = reverseBoundaryPair W (rowVertex F j p) (z j) := by
  have h := JTActualJointChoicePrism.starting_chain_endpoints F j (b F j p)
    (α F j p) (β F j p)
  exact h

/-- The original left cut coefficient at the chain's actual ordinal. -/
def leftCutCoefficient (p : C F j) :=
  std.map (α F j p) ≫ leftCoefficient (L := L) (old F j p) (vertex F j p)

/-- The original right cut coefficient at the chain's actual ordinal. -/
def rightCutCoefficient (p : C F j) :=
  std.map (α F j p) ≫ rightCoefficient (L := L) (old F j p) (vertex F j p)

/-- The exact left cut followed by the chosen full higher ending edge. -/
def leftCoefficients (p : C F j) :
    Coefficients W (cutLeft (code F j p) (vertex F j p)) E (n F j p) x (z j) where
  left := leftCutCoefficient F j p
  right := ending F j p ≫ edgeLabelFromRow W
  seam := by
    dsimp only [leftCutCoefficient, rowVertex]
    rw [Category.assoc, left_last, ← Category.assoc,
      JTWhiskerEdgeCoefficient.first,
      (boundaryPair_endpoints W _ _ (ending_pair F j p)).1]
  first := by
    dsimp only [leftCutCoefficient]
    rw [Category.assoc, left_first]
    rw [← Category.assoc]
    exact congrArg (fun q ↦ q ≫ zeroPoint W x)
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  last := by
    rw [JTWhiskerEdgeCoefficient.last,
      (boundaryPair_endpoints W _ _ (ending_pair F j p)).2,
      Category.assoc, jointLabelFromRow_vertex]

/-- The same chosen edge followed by the original right cut. -/
def rightCoefficients (p : C F j) :
    Coefficients W E (cutRight (code F j p) (vertex F j p)) (n F j p) (z j) y where
  left := starting F j p ≫ edgeLabelFromRow W
  right := rightCutCoefficient F j p
  seam := by
    dsimp only [rightCutCoefficient, rowVertex]
    rw [JTWhiskerEdgeCoefficient.last]
    simp only [Category.assoc]
    rw [right_first]
    simp only [← Category.assoc]
    rw [(reverseBoundaryPair_endpoints W _ _ (starting_pair F j p)).2]
  first := by
    rw [JTWhiskerEdgeCoefficient.first,
      (reverseBoundaryPair_endpoints W _ _ (starting_pair F j p)).1,
      Category.assoc, jointLabelFromRow_vertex]
  last := by
    dsimp only [rightCutCoefficient]
    rw [Category.assoc, right_last]
    rw [← Category.assoc]
    exact congrArg (fun q ↦ q ≫ zeroPoint W y)
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private abbrev markedDiagram :=
  JTActualJointChoiceChainGraph.base F j ⋙ JTActualJointChoiceCover.projection F j
private abbrev originalDiagram :=
  markedDiagram F j ⋙ JTExactlyMarkedSourceDiagram.base F j
private abbrev oldArrow {p q : C F j} (f : p ⟶ q) :=
  (originalDiagram F j).map f

private theorem cut_map {p q : C F j} (f : p ⟶ q) :
    orderMap ((codes L).map (oldArrow F j f)).map (vertex F j p) =
      vertex F j q :=
  JTExactlyMarkedSourceDiagram.cut_map F j ((markedDiagram F j).map f)

private abbrev leftNative {p q : C F j} (f : p ⟶ q) :
    cutLeft (code F j p) (vertex F j p) ⟶
      cutLeft (code F j q) (vertex F j q) :=
  DaggerOriginalProductGadget.cutLeftHom ((codes L).map (oldArrow F j f))
    (vertex F j p) (vertex F j q) (cut_map F j f)

private abbrev rightNative {p q : C F j} (f : p ⟶ q) :
    cutRight (code F j p) (vertex F j p) ⟶
      cutRight (code F j q) (vertex F j q) :=
  DaggerOriginalProductGadget.cutRightHom ((codes L).map (oldArrow F j f))
    (vertex F j p) (vertex F j q) (cut_map F j f)

private abbrev pre {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.{0}.map u) W

private theorem original_natural {p q : C F j} (f : p ⟶ q) :
    (α F j p) ≫ (JTJointRelativeGraphFamily.coefficient (L := L)).map
      (oldArrow F j f) =
      (JTActualJointChoiceChainGraph.ordinals F j).map f ≫ α F j q := by
  have h := (JTActualJointChoiceChainGraph.toOriginal F j).naturality f
  exact h.symm

private theorem leftCut_natural {p q : C F j} (f : p ⟶ q) :
    leftCutCoefficient F j p =
      std.map ((JTActualJointChoiceChainGraph.ordinals F j).map f) ≫
        leftCutCoefficient F j q ≫ pre (leftNative F j f).map := by
  have hc := JTActualJointCutCoefficientTransport.leftCoefficient_map
    (L := L) (oldArrow F j f) (vertex F j p) (vertex F j q) (cut_map F j f)
  change leftCoefficient (L := L) (old F j p) (vertex F j p) =
    std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map (oldArrow F j f)) ≫
      leftCoefficient (L := L) (old F j q) (vertex F j q) ≫
        pre (leftNative F j f).map at hc
  unfold leftCutCoefficient
  rw [hc]
  have hα := congrArg std.map (original_natural F j f)
  simpa only [std.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ leftCoefficient (L := L) (old F j q) (vertex F j q) ≫
      pre (leftNative F j f).map) hα

private theorem rightCut_natural {p q : C F j} (f : p ⟶ q) :
    rightCutCoefficient F j p =
      std.map ((JTActualJointChoiceChainGraph.ordinals F j).map f) ≫
        rightCutCoefficient F j q ≫ pre (rightNative F j f).map := by
  have hc := JTActualJointCutCoefficientTransport.rightCoefficient_map
    (L := L) (oldArrow F j f) (vertex F j p) (vertex F j q) (cut_map F j f)
  change rightCoefficient (L := L) (old F j p) (vertex F j p) =
    std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map (oldArrow F j f)) ≫
      rightCoefficient (L := L) (old F j q) (vertex F j q) ≫
        pre (rightNative F j f).map at hc
  unfold rightCutCoefficient
  rw [hc]
  have hα := congrArg std.map (original_natural F j f)
  simpa only [std.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ rightCoefficient (L := L) (old F j q) (vertex F j q) ≫
      pre (rightNative F j f).map) hα

private theorem pre_id : pre (W := W) (𝟙 E.toSSet) = 𝟙 _ := by
  unfold pre
  rw [show discreteFree.{0}.map (𝟙 E.toSSet) = 𝟙 _ from discreteFree.{0}.map_id _]
  exact diagramMappingPrecomp_id (discreteFree.obj E.toSSet) W

private theorem ending_natural {p q : C F j} (f : p ⟶ q) :
    ending F j p = std.map ((JTActualJointChoiceChainGraph.ordinals F j).map f) ≫
      ending F j q := by
  have h := (JTActualJointChoiceChainGraph.chainEnding F j).naturality f
  simpa only [Category.comp_id] using h.symm

private theorem starting_natural {p q : C F j} (f : p ⟶ q) :
    starting F j p = std.map ((JTActualJointChoiceChainGraph.ordinals F j).map f) ≫
      starting F j q := by
  have h := (JTActualJointChoiceChainGraph.chainStarting F j).naturality f
  simpa only [Category.comp_id] using h.symm

/-- The exact left decorated map on a chain arrow. -/
def leftMap {p q : C F j} (f : p ⟶ q) :
    JTComposedPrismLabels.index (leftCoefficients F j p) ⟶
      JTComposedPrismLabels.index (leftCoefficients F j q) :=
  JTComposedPrismLabelOperators.indexMap (leftCoefficients F j p)
    (leftCoefficients F j q) (leftNative F j f) (𝟙 E)
    ((JTActualJointChoiceChainGraph.ordinals F j).map f)
    (leftCut_natural F j f)
    (by
      change (ending F j p ≫ edgeLabelFromRow W) =
        std.map ((JTActualJointChoiceChainGraph.ordinals F j).map f) ≫
          (ending F j q ≫ edgeLabelFromRow W) ≫ pre (𝟙 E.toSSet)
      rw [pre_id, Category.comp_id, ending_natural F j f, Category.assoc])

/-- The exact right decorated map on the same chain arrow. -/
def rightMap {p q : C F j} (f : p ⟶ q) :
    JTComposedPrismLabels.index (rightCoefficients F j p) ⟶
      JTComposedPrismLabels.index (rightCoefficients F j q) :=
  JTComposedPrismLabelOperators.indexMap (rightCoefficients F j p)
    (rightCoefficients F j q) (𝟙 E) (rightNative F j f)
    ((JTActualJointChoiceChainGraph.ordinals F j).map f)
    (by
      change (starting F j p ≫ edgeLabelFromRow W) =
        std.map ((JTActualJointChoiceChainGraph.ordinals F j).map f) ≫
          (starting F j q ≫ edgeLabelFromRow W) ≫ pre (𝟙 E.toSSet)
      rw [pre_id, Category.comp_id, starting_natural F j f, Category.assoc])
    (rightCut_natural F j f)


private theorem leftNative_id (p : C F j) :
    leftNative F j (𝟙 p) = 𝟙 (cutLeft (code F j p) (vertex F j p)) := by
  change DaggerOriginalProductGadget.cutLeftHom
    ((codes L).map ((originalDiagram F j).map (𝟙 p)))
    (vertex F j p) (vertex F j p) _ = _
  simpa only [(originalDiagram F j).map_id, (codes L).map_id] using
    DaggerOriginalProductGadget.cutLeftHom_id (code F j p) (vertex F j p)

private theorem rightNative_id (p : C F j) :
    rightNative F j (𝟙 p) = 𝟙 (cutRight (code F j p) (vertex F j p)) := by
  change DaggerOriginalProductGadget.cutRightHom
    ((codes L).map ((originalDiagram F j).map (𝟙 p)))
    (vertex F j p) (vertex F j p) _ = _
  simpa only [(originalDiagram F j).map_id, (codes L).map_id] using
    DaggerOriginalProductGadget.cutRightHom_id (code F j p) (vertex F j p)

private theorem leftNative_comp {p q r : C F j} (f : p ⟶ q) (g : q ⟶ r) :
    leftNative F j (f ≫ g) = leftNative F j f ≫ leftNative F j g := by
  change DaggerOriginalProductGadget.cutLeftHom
    ((codes L).map ((originalDiagram F j).map (f ≫ g)))
    (vertex F j p) (vertex F j r) _ = _
  simpa only [(originalDiagram F j).map_comp, (codes L).map_comp] using
    DaggerOriginalProductGadget.cutLeftHom_comp
      ((codes L).map (oldArrow F j f)) ((codes L).map (oldArrow F j g))
      (vertex F j p) (vertex F j q) (vertex F j r)
      (cut_map F j f) (cut_map F j g)

private theorem rightNative_comp {p q r : C F j} (f : p ⟶ q) (g : q ⟶ r) :
    rightNative F j (f ≫ g) = rightNative F j f ≫ rightNative F j g := by
  change DaggerOriginalProductGadget.cutRightHom
    ((codes L).map ((originalDiagram F j).map (f ≫ g)))
    (vertex F j p) (vertex F j r) _ = _
  simpa only [(originalDiagram F j).map_comp, (codes L).map_comp] using
    DaggerOriginalProductGadget.cutRightHom_comp
      ((codes L).map (oldArrow F j f)) ((codes L).map (oldArrow F j g))
      (vertex F j p) (vertex F j q) (vertex F j r)
      (cut_map F j f) (cut_map F j g)

private abbrev leftProjection :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x (z j))
private abbrev rightProjection :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W (z j) y)

private theorem hom_ext {s t : Vertex W}
    {a b : OrderedLabelElements.Index W
      (OrderedNecklaceVertexPoints.boundaryPoint W s t)} {f g : a ⟶ b}
    (h : (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W s t)).map f =
        (OrderedLabelElements.projection W
          (OrderedNecklaceVertexPoints.boundaryPoint W s t)).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

private theorem leftMap_projection {p q : C F j} (f : p ⟶ q) :
    (leftProjection j).map (leftMap F j f) =
      (wedgeMap (leftNative F j f) (𝟙 E),
        (JTActualJointChoiceChainGraph.ordinals F j).map f) := rfl

private theorem rightMap_projection {p q : C F j} (f : p ⟶ q) :
    (rightProjection j).map (rightMap F j f) =
      (wedgeMap (𝟙 E) (rightNative F j f),
        (JTActualJointChoiceChainGraph.ordinals F j).map f) := rfl

/-- The complete corrected left decorated label functor on every higher chain. -/
def leftLabels : C F j ⥤ DecoratedNecklaceHomDiagram.Index W x (z j) where
  obj p := JTComposedPrismLabels.index (leftCoefficients F j p)
  map f := leftMap F j f
  map_id p := by
    apply hom_ext
    rw [leftMap_projection, (leftProjection j).map_id,
      leftNative_id F j p, (JTActualJointChoiceChainGraph.ordinals F j).map_id]
    apply Prod.ext
    · exact wedgeMap_id
    · rfl
  map_comp {p q r} f g := by
    apply hom_ext
    rw [leftMap_projection, (leftProjection j).map_comp,
      leftMap_projection, leftMap_projection,
      leftNative_comp F j f g, (JTActualJointChoiceChainGraph.ordinals F j).map_comp]
    apply Prod.ext
    · simpa only [Category.id_comp] using
        wedgeMap_comp (leftNative F j f) (𝟙 E) (leftNative F j g) (𝟙 E)
    · rfl

/-- The complete corrected right decorated label functor on the same chains. -/
def rightLabels : C F j ⥤ DecoratedNecklaceHomDiagram.Index W (z j) y where
  obj p := JTComposedPrismLabels.index (rightCoefficients F j p)
  map f := rightMap F j f
  map_id p := by
    apply hom_ext
    rw [rightMap_projection, (rightProjection j).map_id,
      rightNative_id F j p, (JTActualJointChoiceChainGraph.ordinals F j).map_id]
    apply Prod.ext
    · exact wedgeMap_id
    · rfl
  map_comp {p q r} f g := by
    apply hom_ext
    rw [rightMap_projection, (rightProjection j).map_comp,
      rightMap_projection, rightMap_projection,
      rightNative_comp F j f g, (JTActualJointChoiceChainGraph.ordinals F j).map_comp]
    apply Prod.ext
    · simpa only [Category.id_comp] using
        wedgeMap_comp (𝟙 E) (rightNative F j f) (𝟙 E) (rightNative F j g)
    · rfl


end
end DaggerModels.PartII.JTActualJointChainSideLabels
