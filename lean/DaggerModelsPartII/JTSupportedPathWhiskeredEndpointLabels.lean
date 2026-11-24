import DaggerModelsPartII.JTSupportedPathWhiskeredGraph
import DaggerModelsPartII.JTSupportedPathChainEndpoints

/-!
# Whole three-piece labels at the supported path endpoints

Reuse: `JTVariableMiddleWhiskeredDiagram.MiddleChange` constructs a natural
decorated comparison from the three literal coefficient equations.
`JTSupportedPathChainEndpoints.coefficientMap_zero/one` supplies the middle
equation at the two fixed interval endpoints. The outer equations are the
definitions of `JTSupportedPathWhiskeredDiagram.pulledLeft/pulledRight`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSupportedPathWhiskeredEndpointLabels

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map f) W

variable {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
variable (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (P R : I ⥤ NecklaceCode)
variable (A : JTSupportedPathWhiskeredDiagram.Surroundings W x z y L P R)

private abbrev First := JTSupportedPathChainLabels.First W z L S u hs
private abbrev Index := JTSupportedPathChainLabels.Index W z L S u hs
private abbrev endpoint (b : Fin 2) :=
  JTSupportedPathChainEndpoints.endpointSection W z L S u hs b
private abbrev original (b : Fin 2) : First W z L S u hs ⥤ I :=
  endpoint W z L S u hs b ⋙ JTSupportedPathChainLabels.toOriginal W z L S u hs
private abbrev endpointDegree (b : Fin 2) :=
  JTSupportedPathChainEndpoints.endpointDegree W z L S u hs b

/-- Reindex all three full coefficients without changing their data. -/
private def reindex {C : Type} [SmallCategory C]
    {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}
    (F : JTVariableMiddleWhiskeredDiagram.Family
      (W := W) (x := x) (y := y) P M R K) (H : C ⥤ I) :
    JTVariableMiddleWhiskeredDiagram.Family
      (W := W) (x := x) (y := y) (H ⋙ P) (H ⋙ M) (H ⋙ R) (H ⋙ K) where
  data c := F.data (H.obj c)
  left_nat f := F.left_nat (H.map f)
  middle_nat f := F.middle_nat (H.map f)
  right_nat f := F.right_nat (H.map f)

private def sourceFamily (b : Fin 2) :=
  reindex W x y
    (JTSupportedPathWhiskeredDiagram.variableMiddleFamily
      W x z y L S u hs P R A) (endpoint W z L S u hs b)

private def oldFamily (b : Fin 2) :=
  reindex W x y (JTSupportedPathWhiskeredGraph.oldFamily W x z y L P R A)
    (original W z L S u hs b)

private def zeroChange : JTVariableMiddleWhiskeredDiagram.MiddleChange
    (sourceFamily W x z y L S u hs P R A 0)
    (oldFamily W x z y L S u hs P R A 0) where
  middle := 𝟙 _
  degree := endpointDegree W z L S u hs 0
  left p := by
    change std.map ((JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpoint W z L S u hs 0).obj p)) ≫
        A.left ((original W z L S u hs 0).obj p) =
      std.map ((endpointDegree W z L S u hs 0).app p) ≫
        A.left ((original W z L S u hs 0).obj p) ≫
          diagramMappingPrecomp
            (ReversalDiscreteFreeColimits.discreteFree.map (𝟙 _)) W
    rw [ReversalDiscreteFreeColimits.discreteFree.map_id,
      diagramMappingPrecomp_id]
    rfl
  center p := by
    change JTSupportedPathChainLabels.coefficientMap W z L S u hs
        ((endpoint W z L S u hs 0).obj p) =
      std.map ((endpointDegree W z L S u hs 0).app p) ≫
        JTSupportedOrderedCoefficientChoices.old W z L
          ((original W z L S u hs 0).obj p) ≫
            diagramMappingPrecomp
              (ReversalDiscreteFreeColimits.discreteFree.map (𝟙 _)) W
    rw [ReversalDiscreteFreeColimits.discreteFree.map_id,
      diagramMappingPrecomp_id]
    simpa only [Category.comp_id, Category.assoc] using
      JTSupportedPathChainEndpoints.coefficientMap_zero W z L S u hs p
  right p := by
    change std.map ((JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpoint W z L S u hs 0).obj p)) ≫
        A.right ((original W z L S u hs 0).obj p) =
      std.map ((endpointDegree W z L S u hs 0).app p) ≫
        A.right ((original W z L S u hs 0).obj p) ≫
          diagramMappingPrecomp
            (ReversalDiscreteFreeColimits.discreteFree.map (𝟙 _)) W
    rw [ReversalDiscreteFreeColimits.discreteFree.map_id,
      diagramMappingPrecomp_id]
    rfl

/-- At time zero the whole three-piece label maps to the unchanged old label.
All three native operators are identities; the coefficient operator is the
endpoint chain's old-degree comparison. -/
def zeroToOld :
    endpoint W z L S u hs 0 ⋙
      JTSupportedPathWhiskeredGraph.pathLabels W x z y L S u hs P R A ⟶
    original W z L S u hs 0 ⋙
      JTSupportedPathWhiskeredGraph.oldLabels W x z y L P R A :=
  (zeroChange W x z y L S u hs P R A).hom

theorem zeroToOld_projection (p : First W z L S u hs) :
    (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
        ((zeroToOld W x z y L S u hs P R A).app p) =
    (wedgeMap (𝟙 (P.obj ((original W z L S u hs 0).obj p)))
      (wedgeMap
        (𝟙 ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs 0).obj p)))
        (𝟙 (R.obj ((original W z L S u hs 0).obj p)))),
      (endpointDegree W z L S u hs 0).app p) :=
  JTVariableMiddleWhiskeredDiagram.MiddleChange.hom_projection
    (zeroChange W x z y L S u hs P R A) p

/-- At the final endpoint, only the middle full coefficient is changed to
the literal constant at the original degree. Both surrounding coefficients
and all native necklaces remain the original ones. -/
def constantData (a : I) : JTThreePieceLabelOperators.Data W
    (P.obj a) ((JTParametrizedTargetFamilies.codes L).obj a) (R.obj a)
    ((JTParametrizedTargetFamilyComparison.degrees L).obj a) x y where
  left := A.left a
  middle := JTSupportedOrderedCoefficientChoices.constant W z L a
  right := A.right a
  left_join := by
    rw [A.inner_left a]
    change SSet.stdSimplex.isTerminalObj₀.from
        (std.obj ((JTParametrizedTargetFamilyComparison.degrees L).obj a)) ≫
          OrderedNecklaceVertexPoints.zeroPoint W z =
      JTConstantOrderedLabel.constantCoefficient W z
        ((JTParametrizedTargetFamilies.codes L).obj a)
        ((JTParametrizedTargetFamilyComparison.degrees L).obj a) ≫
          TripleBeadEndpointLabel.firstRestriction W
            ((JTParametrizedTargetFamilies.codes L).obj a)
    rw [← JTConstantOrderedLabel.coefficient_constantLabel W z
      ((JTParametrizedTargetFamilies.codes L).obj a)
      ((JTParametrizedTargetFamilyComparison.degrees L).obj a)]
    exact (JTOrderedLabelBinaryGlue.coefficient_first W z z
      ((JTParametrizedTargetFamilies.codes L).obj a)
      ((JTParametrizedTargetFamilyComparison.degrees L).obj a)
      (JTConstantOrderedLabel.constantLabel W z
        ((JTParametrizedTargetFamilies.codes L).obj a)
        ((JTParametrizedTargetFamilyComparison.degrees L).obj a))).symm
  right_join := by
    rw [A.inner_right a]
    change JTConstantOrderedLabel.constantCoefficient W z
        ((JTParametrizedTargetFamilies.codes L).obj a)
        ((JTParametrizedTargetFamilyComparison.degrees L).obj a) ≫
          TripleBeadEndpointLabel.lastRestriction W
            ((JTParametrizedTargetFamilies.codes L).obj a) =
      SSet.stdSimplex.isTerminalObj₀.from
        (std.obj ((JTParametrizedTargetFamilyComparison.degrees L).obj a)) ≫
          OrderedNecklaceVertexPoints.zeroPoint W z
    rw [← JTConstantOrderedLabel.coefficient_constantLabel W z
      ((JTParametrizedTargetFamilies.codes L).obj a)
      ((JTParametrizedTargetFamilyComparison.degrees L).obj a)]
    exact JTOrderedLabelBinaryGlue.coefficient_last W z z
      ((JTParametrizedTargetFamilies.codes L).obj a)
      ((JTParametrizedTargetFamilyComparison.degrees L).obj a)
      (JTConstantOrderedLabel.constantLabel W z
        ((JTParametrizedTargetFamilies.codes L).obj a)
        ((JTParametrizedTargetFamilyComparison.degrees L).obj a))
  first := A.global_first a
  last := A.global_last a

/-- The full constant-middle target is a genuine decorated diagram. -/
def constantFamily : JTVariableMiddleWhiskeredDiagram.Family
    (W := W) (x := x) (y := y) P (JTParametrizedTargetFamilies.codes L) R
      (JTParametrizedTargetFamilyComparison.degrees L) where
  data a := constantData W x z y L P R A a
  left_nat g := A.left_nat g
  middle_nat g := JTSupportedOrderedCoefficientChoices.constant_map W z L g
  right_nat g := A.right_nat g

abbrev constantLabels : I ⥤ DecoratedNecklaceHomDiagram.Index W x y :=
  (constantFamily W x z y L P R A).labels

private def oneFamily : JTVariableMiddleWhiskeredDiagram.Family
    (W := W) (x := x) (y := y)
    (original W z L S u hs 1 ⋙ P)
    (original W z L S u hs 1 ⋙ JTParametrizedTargetFamilies.codes L)
    (original W z L S u hs 1 ⋙ R)
    (original W z L S u hs 1 ⋙
      JTParametrizedTargetFamilyComparison.degrees L) :=
  reindex W x y (constantFamily W x z y L P R A)
    (original W z L S u hs 1)

private def oneChange : JTVariableMiddleWhiskeredDiagram.MiddleChange
    (sourceFamily W x z y L S u hs P R A 1)
    (oneFamily W x z y L S u hs P R A) where
  middle := 𝟙 _
  degree := endpointDegree W z L S u hs 1
  left p := by
    change std.map ((JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpoint W z L S u hs 1).obj p)) ≫
        A.left ((original W z L S u hs 1).obj p) =
      std.map ((endpointDegree W z L S u hs 1).app p) ≫
        A.left ((original W z L S u hs 1).obj p) ≫
          diagramMappingPrecomp
            (ReversalDiscreteFreeColimits.discreteFree.map (𝟙 _)) W
    rw [ReversalDiscreteFreeColimits.discreteFree.map_id,
      diagramMappingPrecomp_id]
    rfl
  center p := by
    change JTSupportedPathChainLabels.coefficientMap W z L S u hs
        ((endpoint W z L S u hs 1).obj p) =
      std.map ((endpointDegree W z L S u hs 1).app p) ≫
        JTSupportedOrderedCoefficientChoices.constant W z L
          ((original W z L S u hs 1).obj p) ≫
            diagramMappingPrecomp
              (ReversalDiscreteFreeColimits.discreteFree.map (𝟙 _)) W
    rw [ReversalDiscreteFreeColimits.discreteFree.map_id,
      diagramMappingPrecomp_id]
    simpa only [Category.comp_id, Category.assoc] using
      JTSupportedPathChainEndpoints.coefficientMap_one W z L S u hs p
  right p := by
    change std.map ((JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpoint W z L S u hs 1).obj p)) ≫
        A.right ((original W z L S u hs 1).obj p) =
      std.map ((endpointDegree W z L S u hs 1).app p) ≫
        A.right ((original W z L S u hs 1).obj p) ≫
          diagramMappingPrecomp
            (ReversalDiscreteFreeColimits.discreteFree.map (𝟙 _)) W
    rw [ReversalDiscreteFreeColimits.discreteFree.map_id,
      diagramMappingPrecomp_id]
    rfl

/-- The time-one whole label maps naturally to the unchanged outer labels
with a literal constant middle label in the same native necklace. -/
def oneToConstant :
    endpoint W z L S u hs 1 ⋙
      JTSupportedPathWhiskeredGraph.pathLabels W x z y L S u hs P R A ⟶
    original W z L S u hs 1 ⋙ constantLabels W x z y L P R A :=
  (oneChange W x z y L S u hs P R A).hom

theorem oneToConstant_projection (p : First W z L S u hs) :
    (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
        ((oneToConstant W x z y L S u hs P R A).app p) =
    (wedgeMap (𝟙 (P.obj ((original W z L S u hs 1).obj p)))
      (wedgeMap
        (𝟙 ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs 1).obj p)))
        (𝟙 (R.obj ((original W z L S u hs 1).obj p)))),
      (endpointDegree W z L S u hs 1).app p) :=
  JTVariableMiddleWhiskeredDiagram.MiddleChange.hom_projection
    (oneChange W x z y L S u hs P R A) p

end
end DaggerModels.PartII.JTSupportedPathWhiskeredEndpointLabels
