import DaggerModelsPartII.JTSharedInsertionIncidentEdges
import DaggerModelsPartII.JTActualJointChainSeamSurroundings
import DaggerModelsPartII.JTJointPairGapDiagram
import DaggerModelsPartII.JTThreePieceLabelOperators

/-!
The seam at the inserted cut retains BOTH corrections at the two outer cuts.
Its inner endpoints are the varying old row at the inserted cut; its original
outer endpoints remain x and y. All coefficients use the same actual full chain.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionSeamSurroundings

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue glue_first glue_last
  glue_left glue_right)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev E := single 1
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map f) W

private def wedgeDiagram {C : Type} [SmallCategory C]
    (P R : C ⥤ NecklaceCode) : C ⥤ NecklaceCode where
  obj p := wedge (P.obj p) (R.obj p)
  map f := wedgeMap (P.map f) (R.map f)
  map_id p := by rw [P.map_id, R.map_id]; exact wedgeMap_id
  map_comp f g := by rw [P.map_comp, R.map_comp]; exact wedgeMap_comp _ _ _ _

private theorem glue_natural {W : Source} {T U T' U' : NecklaceCode}
    {k l : SimplexCategory} (f : T ⟶ T') (g : U ⟶ U') (r : k ⟶ l)
    (a : std.obj k ⟶ labels W T) (b : std.obj k ⟶ labels W U)
    (a' : std.obj l ⟶ labels W T') (b' : std.obj l ⟶ labels W U')
    (h : a ≫ lastRestriction W T = b ≫ firstRestriction W U)
    (h' : a' ≫ lastRestriction W T' = b' ≫ firstRestriction W U')
    (ha : a = std.map r ≫ a' ≫ pre W f.map)
    (hb : b = std.map r ≫ b' ≫ pre W g.map) :
    glue W T U k a b h = std.map r ≫ glue W T' U' l a' b' h' ≫
      pre W (wedgeMap f g).map := by
  apply JTThreePieceLabelOperators.wedge_coefficient_map f g r
  · rw [glue_left, ha]
    simp only [← Category.assoc, glue_left]
  · rw [glue_right, hb]
    simp only [← Category.assoc, glue_right]

private theorem reindex_natural {C : Type} [SmallCategory C] {W : Source}
    (N : C ⥤ NecklaceCode) (D K : C ⥤ SimplexCategory) (α : K ⟶ D)
    (c : ∀ p, std.obj (D.obj p) ⟶ labels W (N.obj p))
    (hc : ∀ {p q} (f : p ⟶ q), c p = std.map (D.map f) ≫ c q ≫ pre W (N.map f).map)
    {p q : C} (f : p ⟶ q) :
    std.map (α.app p) ≫ c p = std.map (K.map f) ≫
      (std.map (α.app q) ≫ c q) ≫ pre W (N.map f).map := by
  rw [hc f]
  have h := congrArg std.map (α.naturality f).symm
  simpa only [std.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ c q ≫ pre W (N.map f).map) h

private theorem edge_natural {C : Type} [SmallCategory C] {W : Source}
    (K : C ⥤ SimplexCategory)
    (e : K ⋙ std ⟶ (Functor.const C).obj (row W ⦋1⦌))
    {p q : C} (f : p ⟶ q) :
    e.app p ≫ TwoBeadEndpointLabel.edgeLabelFromRow W = std.map (K.map f) ≫
      (e.app q ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) ≫ pre W (𝟙 E.toSSet) := by
  have hi : pre W (𝟙 E.toSSet) = 𝟙 _ := by
    unfold pre
    rw [discreteFree.map_id]
    exact diagramMappingPrecomp_id _ W
  rw [hi, Category.comp_id]
  have h := e.naturality f
  simpa only [Functor.comp_map, Category.comp_id, Category.assoc] using
    (congrArg (fun t ↦ t ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) h).symm

private theorem rowZero_first (W : Source) :
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

private theorem rowZero_last (W : Source) :
    JTNativeRowLabel.labelFromRow W 0 ≫ lastRestriction W (single 0) =
      TwoBeadEndpointLabel.jointLabelFromRow W := rowZero_first W

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The same full chain and the same single all-vertex tuple at the actual insertion. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The unchanged common chain ordinal. -/
abbrev ordinals := JTSharedInsertionChoices.ordinals F j

/-- The seam remains attached to the actual varying old row at the inserted cut. -/
abbrev seamRows := JTSharedInsertionChainSupport.rows F j 1

private abbrev marks := JTSharedInsertionChainSupport.marks F j
private abbrev originalBase := JTSharedInsertionChainSupport.originalBase F j
private abbrev α := JTSharedInsertionChoices.toOriginal F j
private abbrev insertion (p : Index F j) :=
  (JTSharedInsertionChoices.projection F j).obj ((JTSharedInsertionChoices.base F j).obj p)
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

private theorem pair_ext {a : A} {p q : JTJointPairSourceDiagram.Pair F j a}
    (hl : p.left = q.left) (hr : p.right = q.right) : p = q := by
  cases p; cases q; cases hl; cases hr; rfl

/-- The actual lower interval uses the earlier and inserted vertices of this insertion. -/
def lowerPairs : Index F j ⥤ JTJointPairSourceDiagram.Index F j where
  obj p := ⟨(originalBase F j).obj p,
    ⟨((marks F j 0).obj p).2, ((marks F j 1).obj p).2,
      (insertion F j p).2.property.1⟩⟩
  map f := ⟨(originalBase F j).map f, by
    apply pair_ext F j
    · exact ((marks F j 0).map f).property
    · exact ((marks F j 1).map f).property⟩
  map_id p := by apply CategoryOfElements.ext; exact (originalBase F j).map_id p
  map_comp f g := by apply CategoryOfElements.ext; exact (originalBase F j).map_comp f g

/-- The upper interval uses the inserted and later vertices of the same insertion. -/
def upperPairs : Index F j ⥤ JTJointPairSourceDiagram.Index F j where
  obj p := ⟨(originalBase F j).obj p,
    ⟨((marks F j 1).obj p).2, ((marks F j 2).obj p).2,
      (insertion F j p).2.property.2⟩⟩
  map f := ⟨(originalBase F j).map f, by
    apply pair_ext F j
    · exact ((marks F j 1).map f).property
    · exact ((marks F j 2).map f).property⟩
  map_id p := by apply CategoryOfElements.ext; exact (originalBase F j).map_id p
  map_comp f g := by apply CategoryOfElements.ext; exact (originalBase F j).map_comp f g

/-- The entire old interval from the earlier to the inserted cut, including point cases. -/
abbrev lowerNative := lowerPairs F j ⋙ JTJointPairGapDiagram.native F j

/-- The entire old interval from the inserted to the later cut, including point cases. -/
abbrev upperNative := upperPairs F j ⋙ JTJointPairGapDiagram.native F j

private abbrev leftSide := JTSharedInsertionChoices.earlierChain F j ⋙
  JTActualJointChainSideLabels.leftLabels F j
private abbrev rightSide := JTSharedInsertionChoices.laterChain F j ⋙
  JTActualJointChainSideLabels.rightLabels F j
private abbrev leftOuter := codes (leftSide F j)
private abbrev rightOuter := codes (rightSide F j)
private abbrev edgeDiagram : Index F j ⥤ NecklaceCode := (Functor.const _).obj E

/-- (old prefix at a + ending at a) + (starting at a + old interval [a,b]). -/
abbrev leftNative := wedgeDiagram (leftOuter F j)
  (wedgeDiagram (edgeDiagram F j) (lowerNative F j))

/-- old interval [b,c] + (ending at c + (starting at c + old suffix at c)). -/
abbrev rightNative := wedgeDiagram (upperNative F j)
  (wedgeDiagram (edgeDiagram F j) (rightOuter F j))

private abbrev correctedLeft (p : Index F j) :=
  JTOrderedLabelBinaryGlue.coefficient W x (z j) ((leftOuter F j).obj p)
    ((ordinals F j).obj p) ((leftSide F j).obj p).unop.2
private abbrev correctedRight (p : Index F j) :=
  JTOrderedLabelBinaryGlue.coefficient W (z j) y ((rightOuter F j).obj p)
    ((ordinals F j).obj p) ((rightSide F j).obj p).unop.2
private abbrev startA (p : Index F j) :=
  (JTSharedInsertionIncidentEdges.starting F j 0).app p ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
private abbrev endC (p : Index F j) :=
  (JTSharedInsertionIncidentEdges.ending F j 2).app p ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
private abbrev lowerCoefficient (p : Index F j) :=
  std.map ((α F j).app p) ≫ JTJointPairGapDiagram.coefficient F j ((lowerPairs F j).obj p)
private abbrev upperCoefficient (p : Index F j) :=
  std.map ((α F j).app p) ≫ JTJointPairGapDiagram.coefficient F j ((upperPairs F j).obj p)

private theorem lower_first (p : Index F j) :
    lowerCoefficient F j p ≫ firstRestriction W ((lowerNative F j).obj p) =
      (JTSharedInsertionChainSupport.rows F j 0).app p ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  dsimp only [lowerCoefficient, lowerNative, Functor.comp_obj,
    JTJointPairGapDiagram.native, JTJointPairGapDiagram.coefficient]
  rw [Category.assoc, JTActualJointGapPrism.coefficient_first]
  rfl

private theorem lower_last (p : Index F j) :
    lowerCoefficient F j p ≫ lastRestriction W ((lowerNative F j).obj p) =
      (seamRows F j).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  dsimp only [lowerCoefficient, lowerNative, Functor.comp_obj,
    JTJointPairGapDiagram.native, JTJointPairGapDiagram.coefficient]
  rw [Category.assoc, JTActualJointGapPrism.coefficient_last]
  rfl

private theorem upper_first (p : Index F j) :
    upperCoefficient F j p ≫ firstRestriction W ((upperNative F j).obj p) =
      (seamRows F j).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  dsimp only [upperCoefficient, upperNative, Functor.comp_obj,
    JTJointPairGapDiagram.native, JTJointPairGapDiagram.coefficient]
  rw [Category.assoc, JTActualJointGapPrism.coefficient_first]
  rfl

private theorem upper_last (p : Index F j) :
    upperCoefficient F j p ≫ lastRestriction W ((upperNative F j).obj p) =
      (JTSharedInsertionChainSupport.rows F j 2).app p ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  dsimp only [upperCoefficient, upperNative, Functor.comp_obj,
    JTJointPairGapDiagram.native, JTJointPairGapDiagram.coefficient]
  rw [Category.assoc, JTActualJointGapPrism.coefficient_last]
  rfl

private theorem startA_last (p : Index F j) :
    startA F j p ≫ lastRestriction W E =
      (JTSharedInsertionChainSupport.rows F j 0).app p ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  rw [JTWhiskerEdgeCoefficient.last,
    (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.starting_endpoints F j 0 p)).2]

private theorem startA_first (p : Index F j) :
    startA F j p ≫ firstRestriction W E =
      term (std.obj ((ordinals F j).obj p)) ≫ OrderedNecklaceVertexPoints.zeroPoint W (z j) := by
  rw [JTWhiskerEdgeCoefficient.first,
    (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.starting_endpoints F j 0 p)).1,
    Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]

private theorem endC_first (p : Index F j) :
    endC F j p ≫ firstRestriction W E =
      (JTSharedInsertionChainSupport.rows F j 2).app p ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  rw [JTWhiskerEdgeCoefficient.first,
    (JTJointEndpointRelativeLift.boundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.ending_endpoints F j 2 p)).1]

private theorem endC_last (p : Index F j) :
    endC F j p ≫ lastRestriction W E =
      term (std.obj ((ordinals F j).obj p)) ≫ OrderedNecklaceVertexPoints.zeroPoint W (z j) := by
  rw [JTWhiskerEdgeCoefficient.last,
    (JTJointEndpointRelativeLift.boundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.ending_endpoints F j 2 p)).2,
    Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]

private theorem leftInner_join (p : Index F j) :
    startA F j p ≫ lastRestriction W E =
      lowerCoefficient F j p ≫ firstRestriction W ((lowerNative F j).obj p) := by
  rw [startA_last, lower_first]

private def leftInner (p : Index F j) :=
  glue W E ((lowerNative F j).obj p) ((ordinals F j).obj p)
    (startA F j p) (lowerCoefficient F j p) (leftInner_join F j p)

private theorem leftOuter_join (p : Index F j) :
    correctedLeft F j p ≫ lastRestriction W ((leftOuter F j).obj p) =
      leftInner F j p ≫ firstRestriction W (wedge E ((lowerNative F j).obj p)) := by
  rw [leftInner, glue_first, startA_first]
  exact JTOrderedLabelBinaryGlue.coefficient_last W x (z j) _ _ _

/-- The entire modified left surrounding coefficient, retaining both corrections at a. -/
def leftCoefficient (p : Index F j) :=
  glue W ((leftOuter F j).obj p) (wedge E ((lowerNative F j).obj p))
    ((ordinals F j).obj p) (correctedLeft F j p) (leftInner F j p) (leftOuter_join F j p)

private theorem rightInner_join (p : Index F j) :
    endC F j p ≫ lastRestriction W E =
      correctedRight F j p ≫ firstRestriction W ((rightOuter F j).obj p) := by
  rw [endC_last]
  exact (JTOrderedLabelBinaryGlue.coefficient_first W (z j) y _ _ _).symm

private def rightInner (p : Index F j) :=
  glue W E ((rightOuter F j).obj p) ((ordinals F j).obj p)
    (endC F j p) (correctedRight F j p) (rightInner_join F j p)

private theorem rightOuter_join (p : Index F j) :
    upperCoefficient F j p ≫ lastRestriction W ((upperNative F j).obj p) =
      rightInner F j p ≫ firstRestriction W (wedge E ((rightOuter F j).obj p)) := by
  rw [rightInner, glue_first, endC_first, upper_last]

/-- The entire modified right surrounding coefficient, retaining both corrections at c. -/
def rightCoefficient (p : Index F j) :=
  glue W ((upperNative F j).obj p) (wedge E ((rightOuter F j).obj p))
    ((ordinals F j).obj p) (upperCoefficient F j p) (rightInner F j p) (rightOuter_join F j p)

private theorem correctedLeft_natural {p q : Index F j} (f : p ⟶ q) :
    correctedLeft F j p = std.map ((ordinals F j).map f) ≫
      correctedLeft F j q ≫ pre W ((leftOuter F j).map f).map :=
  JTOrderedLabelWedge.coefficient_of_indexHom
    ((leftSide F j).obj p).unop.2 ((leftSide F j).obj q).unop.2
    ((leftOuter F j).map f) ((ordinals F j).map f) ((leftSide F j).map f) (by rfl)

private theorem correctedRight_natural {p q : Index F j} (f : p ⟶ q) :
    correctedRight F j p = std.map ((ordinals F j).map f) ≫
      correctedRight F j q ≫ pre W ((rightOuter F j).map f).map :=
  JTOrderedLabelWedge.coefficient_of_indexHom
    ((rightSide F j).obj p).unop.2 ((rightSide F j).obj q).unop.2
    ((rightOuter F j).map f) ((ordinals F j).map f) ((rightSide F j).map f) (by rfl)

private theorem lower_natural {p q : Index F j} (f : p ⟶ q) :
    lowerCoefficient F j p = std.map ((ordinals F j).map f) ≫
      lowerCoefficient F j q ≫ pre W ((lowerNative F j).map f).map :=
  reindex_natural (lowerNative F j)
    (lowerPairs F j ⋙ JTJointPairSourceDiagram.base F j ⋙
      JTJointRelativeGraphFamily.coefficient (L := L))
    (ordinals F j) (α F j)
    (fun p ↦ JTJointPairGapDiagram.coefficient F j ((lowerPairs F j).obj p))
    (fun f ↦ JTJointPairGapDiagram.coefficient_map F j ((lowerPairs F j).map f)) f

private theorem upper_natural {p q : Index F j} (f : p ⟶ q) :
    upperCoefficient F j p = std.map ((ordinals F j).map f) ≫
      upperCoefficient F j q ≫ pre W ((upperNative F j).map f).map :=
  reindex_natural (upperNative F j)
    (upperPairs F j ⋙ JTJointPairSourceDiagram.base F j ⋙
      JTJointRelativeGraphFamily.coefficient (L := L))
    (ordinals F j) (α F j)
    (fun p ↦ JTJointPairGapDiagram.coefficient F j ((upperPairs F j).obj p))
    (fun f ↦ JTJointPairGapDiagram.coefficient_map F j ((upperPairs F j).map f)) f

private theorem leftInner_natural {p q : Index F j} (f : p ⟶ q) :
    leftInner F j p = std.map ((ordinals F j).map f) ≫ leftInner F j q ≫
      pre W ((wedgeDiagram (edgeDiagram F j) (lowerNative F j)).map f).map := by
  apply glue_natural (𝟙 E) ((lowerNative F j).map f) ((ordinals F j).map f)
  · exact edge_natural (ordinals F j) (JTSharedInsertionIncidentEdges.starting F j 0) f
  · exact lower_natural F j f

private theorem rightInner_natural {p q : Index F j} (f : p ⟶ q) :
    rightInner F j p = std.map ((ordinals F j).map f) ≫ rightInner F j q ≫
      pre W ((wedgeDiagram (edgeDiagram F j) (rightOuter F j)).map f).map := by
  apply glue_natural (𝟙 E) ((rightOuter F j).map f) ((ordinals F j).map f)
  · exact edge_natural (ordinals F j) (JTSharedInsertionIncidentEdges.ending F j 2) f
  · exact correctedRight_natural F j f

private theorem left_natural {p q : Index F j} (f : p ⟶ q) :
    leftCoefficient F j p = std.map ((ordinals F j).map f) ≫
      leftCoefficient F j q ≫ pre W ((leftNative F j).map f).map := by
  apply glue_natural ((leftOuter F j).map f)
    ((wedgeDiagram (edgeDiagram F j) (lowerNative F j)).map f) ((ordinals F j).map f)
  · exact correctedLeft_natural F j f
  · exact leftInner_natural F j f

private theorem right_natural {p q : Index F j} (f : p ⟶ q) :
    rightCoefficient F j p = std.map ((ordinals F j).map f) ≫
      rightCoefficient F j q ≫ pre W ((rightNative F j).map f).map := by
  apply glue_natural ((upperNative F j).map f)
    ((wedgeDiagram (edgeDiagram F j) (rightOuter F j)).map f) ((ordinals F j).map f)
  · exact upper_natural F j f
  · exact rightInner_natural F j f

/-- Actual modified surroundings retain outer a,c corrections and the varying seam row at b. -/
def surroundings : JTChosenSeamChainDiagram.Surroundings W (ordinals F j) (seamRows F j)
    (leftNative F j) (rightNative F j) x y where
  left := leftCoefficient F j
  right := rightCoefficient F j
  left_join p := by
    dsimp only [leftNative, wedgeDiagram, edgeDiagram, Functor.const_obj_obj]
    rw [leftCoefficient, glue_last, leftInner, glue_last, lower_last,
      Category.assoc, rowZero_first]
  right_join p := by
    dsimp only [rightNative, wedgeDiagram, edgeDiagram, Functor.const_obj_obj]
    rw [rightCoefficient, glue_first, upper_first, Category.assoc, rowZero_last]
  first p := by
    dsimp only [leftNative, wedgeDiagram, edgeDiagram, Functor.const_obj_obj]
    rw [leftCoefficient, glue_first]
    exact JTOrderedLabelBinaryGlue.coefficient_first W x (z j) _ _ _
  last p := by
    dsimp only [rightNative, wedgeDiagram, edgeDiagram, Functor.const_obj_obj]
    rw [rightCoefficient, glue_last, rightInner, glue_last]
    exact JTOrderedLabelBinaryGlue.coefficient_last W (z j) y _ _ _
  left_nat f := left_natural F j f
  right_nat f := right_natural F j f

end
end DaggerModels.PartII.JTSharedInsertionSeamSurroundings
