import DaggerModelsPartII.JTJointPairChainDiagram
import DaggerModelsPartII.JTJointPairGapDiagram
import DaggerModelsPartII.JTActualJointChainSideLabels
import DaggerModelsPartII.JTComposedPrismLabelOperators

/-! The whole old interval with both chosen higher edge labels on common chains. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointPairGapChainLabels

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue
  glue_first glue_last glue_left glue_right wedgeMappingPullback)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev E := single 1
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointPairChainDiagram.Index F j
private abbrev pair (p : I F j) :=
  (JTJointPairChoiceCover.projection F j).obj ((JTJointPairChainDiagram.base F j).obj p)
private abbrev earlier (p : I F j) := (JTJointPairChainDiagram.earlier F j).obj p
private abbrev later (p : I F j) := (JTJointPairChainDiagram.later F j).obj p
private abbrev n (p : I F j) := (JTJointPairChainDiagram.ordinals F j).obj p
private abbrev α (p : I F j) := (JTJointPairChainDiagram.toOriginal F j).app p
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev B (p : I F j) := JTJointPairGapDiagram.code F j (pair F j p)
private abbrev oldCoefficient (p : I F j) :=
  JTJointPairGapDiagram.coefficient F j (pair F j p)
private abbrev front (p : I F j) :=
  (JTActualJointChainSideLabels.rightCoefficients F j (earlier F j p)).left
private abbrev back (p : I F j) :=
  (JTActualJointChainSideLabels.leftCoefficients F j (later F j p)).right

/-- The original ordered pair and its full interval, reindexed on common chains. -/
abbrev oldPairs : I F j ⥤ JTJointPairSourceDiagram.Index F j :=
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j

/-- The unchanged whole old interval native diagram. -/
abbrev oldNative : I F j ⥤ NecklaceCode :=
  oldPairs F j ⋙ JTJointPairGapDiagram.native F j

/-- The padded native necklace on every common full chain. -/
abbrev code (p : I F j) := wedge E (wedge (B F j p) E)

/-- The exact native map, retaining the whole interior interval. -/
def codeMap {p q : I F j} (f : p ⟶ q) : code F j p ⟶ code F j q :=
  wedgeMap (𝟙 E) (wedgeMap ((oldNative F j).map f) (𝟙 E))

/-- Both relative edges and the old interval are natural in every common chain arrow. -/
def native : I F j ⥤ NecklaceCode where
  obj := code F j
  map := codeMap F j
  map_id p := by
    unfold codeMap
    rw [(oldNative F j).map_id]
    have hi := wedgeMap_id (T := B F j p) (U := E)
    have ho := wedgeMap_id (T := E) (U := wedge (B F j p) E)
    exact (congrArg (wedgeMap (𝟙 E)) hi).trans ho
  map_comp {p q r} f g := by
    unfold codeMap
    rw [(oldNative F j).map_comp]
    have hi := wedgeMap_comp ((oldNative F j).map f) (𝟙 E)
      ((oldNative F j).map g) (𝟙 E)
    have ho := wedgeMap_comp (𝟙 E)
      (wedgeMap ((oldNative F j).map f) (𝟙 E)) (𝟙 E)
      (wedgeMap ((oldNative F j).map g) (𝟙 E))
    exact (congrArg (wedgeMap (𝟙 E)) hi).trans ho

/-- The exact old gap coefficient at the common full-chain ordinal. -/
def gapCoefficient (p : I F j) : std.obj (n F j p) ⟶ labels W (B F j p) :=
  std.map (α F j p) ≫ oldCoefficient F j p

private theorem backJoin (p : I F j) :
    gapCoefficient F j p ≫ lastRestriction W (B F j p) =
      back F j p ≫ firstRestriction W E := by
  unfold gapCoefficient
  rw [Category.assoc, JTActualJointGapPrism.coefficient_last,
    ← JTActualJointCutPrism.left_last]
  exact (JTActualJointChainSideLabels.leftCoefficients F j (later F j p)).seam

private def inside (p : I F j) :=
  glue W (B F j p) E (n F j p) (gapCoefficient F j p) (back F j p)
    (backJoin F j p)

private theorem frontJoin (p : I F j) :
    front F j p ≫ lastRestriction W E =
      inside F j p ≫ firstRestriction W (wedge (B F j p) E) := by
  rw [inside, glue_first]
  unfold gapCoefficient
  rw [Category.assoc, JTActualJointGapPrism.coefficient_first,
    ← JTActualJointCutPrism.right_first]
  exact (JTActualJointChainSideLabels.rightCoefficients F j (earlier F j p)).seam

/-- The front choice, whole old interval, and back choice share one full degree. -/
def coefficients (p : I F j) :
    JTComposedPrismLabels.Coefficients W E (wedge (B F j p) E) (n F j p)
      (z j) (z j) where
  left := front F j p
  right := inside F j p
  seam := frontJoin F j p
  first := (JTActualJointChainSideLabels.rightCoefficients F j (earlier F j p)).first
  last := by
    rw [inside, glue_last]
    exact (JTActualJointChainSideLabels.leftCoefficients F j (later F j p)).last

private theorem original_natural {p q : I F j} (f : p ⟶ q) :
    α F j p ≫ (JTJointPairChainDiagram.coefficient F j).map
      ((JTJointPairChainDiagram.base F j).map f) =
      (JTJointPairChainDiagram.ordinals F j).map f ≫ α F j q :=
  ((JTJointPairChainDiagram.toOriginal F j).naturality f).symm

/-- The full old gap coefficient is natural at every common chain degree. -/
theorem gapCoefficient_map {p q : I F j} (f : p ⟶ q) :
    gapCoefficient F j p =
      std.map ((JTJointPairChainDiagram.ordinals F j).map f) ≫
        gapCoefficient F j q ≫ pre W ((oldNative F j).map f).map := by
  let f' := (oldPairs F j).map f
  have hc := JTJointPairGapDiagram.coefficient_map F j f'
  change oldCoefficient F j p =
    std.map ((JTJointPairChainDiagram.coefficient F j).map
      ((JTJointPairChainDiagram.base F j).map f)) ≫
      oldCoefficient F j q ≫ pre W ((oldNative F j).map f).map at hc
  unfold gapCoefficient
  rw [hc]
  have hα := congrArg std.map (original_natural F j f)
  simpa only [std.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ oldCoefficient F j q ≫
      pre W ((oldNative F j).map f).map) hα

private theorem front_natural {p q : I F j} (f : p ⟶ q) :
    front F j p = std.map ((JTJointPairChainDiagram.ordinals F j).map f) ≫
      front F j q := by
  have h := (JTActualJointChoiceChainGraph.chainStarting F j).naturality
    ((JTJointPairChainDiagram.earlier F j).map f)
  simpa only [Category.comp_id] using congrArg
    (fun u ↦ u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) h.symm

private theorem back_natural {p q : I F j} (f : p ⟶ q) :
    back F j p = std.map ((JTJointPairChainDiagram.ordinals F j).map f) ≫
      back F j q := by
  have h := (JTActualJointChoiceChainGraph.chainEnding F j).naturality
    ((JTJointPairChainDiagram.later F j).map f)
  simpa only [Category.comp_id] using congrArg
    (fun u ↦ u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) h.symm

private theorem pre_id : pre (W := W) (𝟙 E.toSSet) = 𝟙 _ := by
  unfold pre
  rw [show discreteFree.map (𝟙 E.toSSet) = 𝟙 _ from discreteFree.map_id _]
  exact diagramMappingPrecomp_id (discreteFree.obj E.toSSet) W

private theorem front_map {p q : I F j} (f : p ⟶ q) :
    front F j p = std.map ((JTJointPairChainDiagram.ordinals F j).map f) ≫
      front F j q ≫ pre W (𝟙 E.toSSet) := by
  simpa only [pre_id, Category.comp_id] using front_natural F j f

private theorem inside_map {p q : I F j} (f : p ⟶ q) :
    inside F j p = std.map ((JTJointPairChainDiagram.ordinals F j).map f) ≫
      inside F j q ≫
        pre W (wedgeMap ((oldNative F j).map f) (𝟙 E)).map := by
  let g := (oldNative F j).map f
  let r := (JTJointPairChainDiagram.ordinals F j).map f
  apply (wedgeMappingPullback W (B F j p) E).hom_ext
  · rw [inside, glue_left, gapCoefficient_map]
    have hp : pre W (wedgeMap g (𝟙 E)).map ≫
        pre W (wedgeιLeft (B F j p) E) =
        pre W (wedgeιLeft (B F j q) E) ≫ pre W g.map := by
      rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
        ← discreteFree.map_comp, ← discreteFree.map_comp, wedgeMap_left]
      rfl
    simp only [Category.assoc]
    change _ = std.map r ≫ inside F j q ≫
      (pre W (wedgeMap g (𝟙 E)).map ≫ pre W (wedgeιLeft (B F j p) E))
    rw [hp, ← Category.assoc (inside F j q), inside, glue_left]
  · rw [inside, glue_right, back_natural F j f]
    have hp : pre W (wedgeMap g (𝟙 E)).map ≫
        pre W (wedgeιRight (B F j p) E) =
        pre W (wedgeιRight (B F j q) E) ≫ pre W (𝟙 E.toSSet) := by
      rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
        ← discreteFree.map_comp, ← discreteFree.map_comp, wedgeMap_right]
      rfl
    simp only [Category.assoc]
    change _ = std.map r ≫ inside F j q ≫
      (pre W (wedgeMap g (𝟙 E)).map ≫ pre W (wedgeιRight (B F j p) E))
    rw [hp, pre_id, Category.comp_id, inside, glue_right]

/-- The exact decorated map on a common pair chain arrow. -/
def labelMap {p q : I F j} (f : p ⟶ q) :
    JTComposedPrismLabels.index (coefficients F j p) ⟶
      JTComposedPrismLabels.index (coefficients F j q) :=
  JTComposedPrismLabelOperators.indexMap (coefficients F j p)
    (coefficients F j q) (𝟙 E)
    (wedgeMap ((oldNative F j).map f) (𝟙 E))
    ((JTJointPairChainDiagram.ordinals F j).map f)
    (by
      change front F j p =
        std.map ((JTJointPairChainDiagram.ordinals F j).map f) ≫
          front F j q ≫ pre W (𝟙 E.toSSet)
      simpa only [pre_id, Category.comp_id] using front_natural F j f)
    (inside_map F j f)

/-- The entire padded coefficient respects both native and ordinal operators. -/
theorem coefficient_map {p q : I F j} (f : p ⟶ q) :
    JTComposedPrismLabels.coefficient (coefficients F j p) =
      std.map ((JTJointPairChainDiagram.ordinals F j).map f) ≫
        JTComposedPrismLabels.coefficient (coefficients F j q) ≫
          pre W (codeMap F j f).map :=
  JTComposedPrismLabelOperators.coefficient_map
    (coefficients F j p) (coefficients F j q) (𝟙 E)
    (wedgeMap ((oldNative F j).map f) (𝟙 E))
    ((JTJointPairChainDiagram.ordinals F j).map f)
    (front_map F j f) (inside_map F j f)

private abbrev projection :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W (z j) (z j))

private theorem hom_ext
    {a b : OrderedLabelElements.Index W
      (OrderedNecklaceVertexPoints.boundaryPoint W (z j) (z j))}
    {f g : a ⟶ b} (h : (projection j).map f = (projection j).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

private theorem labelMap_projection {p q : I F j} (f : p ⟶ q) :
    (projection j).map (labelMap F j f) =
      (codeMap F j f, (JTJointPairChainDiagram.ordinals F j).map f) := rfl

/-- The complete padded gap label diagram on every simultaneous higher chain. -/
def labels : I F j ⥤ DecoratedNecklaceHomDiagram.Index W (z j) (z j) where
  obj p := JTComposedPrismLabels.index (coefficients F j p)
  map f := labelMap F j f
  map_id p := by
    apply hom_ext
    rw [labelMap_projection, (projection j).map_id]
    apply Prod.ext
    · exact (native F j).map_id p
    · exact (JTJointPairChainDiagram.ordinals F j).map_id p
  map_comp {p q r} f g := by
    apply hom_ext
    rw [labelMap_projection, (projection j).map_comp,
      labelMap_projection, labelMap_projection]
    apply Prod.ext
    · exact (native F j).map_comp f g
    · exact (JTJointPairChainDiagram.ordinals F j).map_comp f g

/-- The label functor retains the exact padded native code. -/
theorem labels_codes : codes (labels F j) = native F j := rfl

/-- Its ordered point has precisely the constructed three-piece coefficient. -/
theorem orderedPoint_coefficient (p : I F j) :
    JTRealizedLabelEndpoints.orderedLabel W (z j) (z j) (code F j p) (n F j p)
      (JTComposedPrismLabels.orderedPoint (coefficients F j p)) =
        SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (coefficients F j p)) :=
  JTComposedPrismLabels.orderedPoint_coefficient (coefficients F j p)

/-- The exact inclusions of the front edge, old interval, and back edge. -/
abbrev frontInclusion (p : I F j) : E.toSSet ⟶ (code F j p).toSSet :=
  wedgeιLeft E (wedge (B F j p) E)

abbrev interiorInclusion (p : I F j) :
    (B F j p).toSSet ⟶ (code F j p).toSSet :=
  wedgeιLeft (B F j p) E ≫ wedgeιRight E (wedge (B F j p) E)

abbrev backInclusion (p : I F j) : E.toSSet ⟶ (code F j p).toSSet :=
  wedgeιRight (B F j p) E ≫ wedgeιRight E (wedge (B F j p) E)

/-- Restriction to the old interval retains every original gap coefficient. -/
theorem coefficient_interior (p : I F j) :
    JTComposedPrismLabels.coefficient (coefficients F j p) ≫
      pre W (interiorInclusion F j p) = gapCoefficient F j p := by
  have hpre : pre W (interiorInclusion F j p) =
      pre W (wedgeιRight E (wedge (B F j p) E)) ≫
        pre W (wedgeιLeft (B F j p) E) := by
    change diagramMappingPrecomp
      (discreteFree.map (wedgeιLeft (B F j p) E ≫
        wedgeιRight E (wedge (B F j p) E))) W = _
    rw [discreteFree.map_comp, diagramMappingPrecomp_comp]
  rw [hpre, ← Category.assoc, JTComposedPrismLabels.coefficient, glue_right]
  exact glue_left W (B F j p) E (n F j p)
    (gapCoefficient F j p) (back F j p) (backJoin F j p)

/-- The two added edges retain their respective chosen chain labels. -/
theorem coefficient_front (p : I F j) :
    JTComposedPrismLabels.coefficient (coefficients F j p) ≫
      pre W (frontInclusion F j p) = front F j p := by
  exact glue_left W E (wedge (B F j p) E) (n F j p)
    (front F j p) (inside F j p) (frontJoin F j p)

theorem coefficient_back (p : I F j) :
    JTComposedPrismLabels.coefficient (coefficients F j p) ≫
      pre W (backInclusion F j p) = back F j p := by
  have hpre : pre W (backInclusion F j p) =
      pre W (wedgeιRight E (wedge (B F j p) E)) ≫
        pre W (wedgeιRight (B F j p) E) := by
    change diagramMappingPrecomp
      (discreteFree.map (wedgeιRight (B F j p) E ≫
        wedgeιRight E (wedge (B F j p) E))) W = _
    rw [discreteFree.map_comp, diagramMappingPrecomp_comp]
  rw [hpre, ← Category.assoc, JTComposedPrismLabels.coefficient, glue_right]
  exact glue_right W (B F j p) E (n F j p)
    (gapCoefficient F j p) (back F j p) (backJoin F j p)

end
end DaggerModels.PartII.JTJointPairGapChainLabels
