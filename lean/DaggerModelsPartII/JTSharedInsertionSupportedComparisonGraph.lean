import DaggerModelsPartII.JTSharedInsertionCoarseSupportedPresentation
import DaggerModelsPartII.JTSharedInsertionCoarseGraphComparison
import DaggerModelsPartII.JTPrismChainGraphTransport

/-!
# Every old graph assignment over the actual supported coarse path

The original old graph is covered by all supported coefficient lifts. Its canonical map
into the checked coarse path graph retains the entire original time and lifted parameter.
No raw equation, section, weak graph map, or new Family is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionSupportedComparisonGraph

noncomputable section

private abbrev J := GroupoidSimplex.parameter

private def ParameterEquation {I : Type} [SmallCategory I]
    {X Y : I ⥤ SSet.{0}} {K : I ⥤ SimplexCategory}
    (px : X ⟶ K ⋙ J) (py : Y ⟶ K ⋙ J) (c : X ⟶ Y) : Prop := c ≫ py = px

private theorem whisker_identity {B : Type} [SmallCategory B] (D : B ⥤ SimplexCategory) :
    Functor.whiskerRight (𝟙 D) J = 𝟙 (D ⋙ J) := by
  apply NatTrans.ext
  funext p
  exact J.map_id _

private theorem identity_parameter {B : Type} [SmallCategory B]
    (X Y : B ⥤ SSet.{0}) {K D : B ⥤ SimplexCategory}
    (px : X ⟶ K ⋙ J) (py : Y ⟶ K ⋙ J) (alpha : D ⟶ K)
    (c : X ⟶ Y) (hc : c ≫ py = px) :
    JTPrismChainGraphTransport.map X Y px py alpha alpha (𝟙 D)
        (Category.id_comp _) c hc ≫ JTPrismChainGraphCover.parameter Y py alpha =
      JTPrismChainGraphCover.parameter X px alpha := by
  have h := JTPrismChainGraphTransport.map_parameter X Y px py alpha alpha (𝟙 D)
    (Category.id_comp _) c hc
  simpa only [whisker_identity, Category.comp_id] using h

private def parameterLeft {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) {X : I ⥤ SSet.{0}} {K : I ⥤ SimplexCategory}
    (p : X ⟶ K ⋙ J) : b ⋙ X ⟶ (b ⋙ K) ⋙ J :=
  Functor.whiskerLeft b p

private theorem parameterLeft_square {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) {X Y : I ⥤ SSet.{0}} {K : I ⥤ SimplexCategory}
    (px : X ⟶ K ⋙ J) (py : Y ⟶ K ⋙ J) (c : X ⟶ Y) (hc : c ≫ py = px) :
    Functor.whiskerLeft b c ≫ parameterLeft b py = parameterLeft b px :=
  congrArg (Functor.whiskerLeft b) hc

private theorem composite_square {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) {X Y U V : I ⥤ SSet.{0}} (g : X ⟶ Y)
    (px : X ⟶ U) (py : Y ⟶ V) (c : U ⟶ V) (h : g ≫ py = px ≫ c)
    {N P : B ⥤ SSet.{0}} (mu : N ⟶ b ⋙ X) (nu : P ⟶ b ⋙ Y)
    (eta : N ⟶ P) (he : eta ≫ nu = mu ≫ Functor.whiskerLeft b g) :
    eta ≫ (nu ≫ Functor.whiskerLeft b py) =
      (mu ≫ Functor.whiskerLeft b px) ≫ Functor.whiskerLeft b c := by
  rw [← Category.assoc, he, Category.assoc, ← Functor.whiskerLeft_comp, h,
    Functor.whiskerLeft_comp, ← Category.assoc]

private theorem composite_trivial {B : Type} [SmallCategory B]
    (X Z : B ⥤ SSet.{0}) {K D : B ⥤ SimplexCategory}
    (p : X ⟶ K ⋙ J) (alpha : D ⟶ K) (pi : X ⟶ Z)
    (ha : ∀ b, Function.Surjective (alpha.app b).toOrderHom)
    (hp : ∀ b, trivialFibrations SSet.{0} (pi.app b)) (b : B) :
    trivialFibrations SSet.{0}
      ((JTPrismChainGraphCover.projection X p alpha ≫ pi).app b) :=
  (trivialFibrations SSet.{0}).comp_mem _ _
    (JTPrismChainGraphCover.projection_trivialFibration X p alpha ha b) (hp b)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

section Factories

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory) (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees M)
variable (hs : ∀ p : I, SSet.stdSimplex.map (u.app p) ≫
  JTSupportedOrderedCoefficientChoices.old W z M p =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z M S p)

private abbrev b := JTSupportedPathChainLabels.toOriginal W z M S u hs
private abbrev alpha := JTSupportedPathChainLabels.toOldCoefficient W z M S u hs

variable {X Y Z T : I ⥤ SSet.{0}} (px : X ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
variable (py : Y ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
variable (c : X ⟶ Y) (hc : ParameterEquation px py c)

private def pathMap := JTPrismChainGraphTransport.map
  (k := b W z M S u hs ⋙ JTParametrizedTargetFamilyComparison.degrees M)
  (b W z M S u hs ⋙ X) (b W z M S u hs ⋙ Y)
  (parameterLeft (b W z M S u hs) px)
  (parameterLeft (b W z M S u hs) py)
  (alpha W z M S u hs) (alpha W z M S u hs)
  (𝟙 (JTSupportedPathChainLabels.ordinals W z M S u hs))
  (Category.id_comp _) (Functor.whiskerLeft (b W z M S u hs) c)
  (parameterLeft_square (b W z M S u hs) px py c hc)

private def pathMap_toOld := JTPrismChainGraphTransport.map_projection
  (k := b W z M S u hs ⋙ JTParametrizedTargetFamilyComparison.degrees M)
  (b W z M S u hs ⋙ X) (b W z M S u hs ⋙ Y)
  (parameterLeft (b W z M S u hs) px)
  (parameterLeft (b W z M S u hs) py)
  (alpha W z M S u hs) (alpha W z M S u hs)
  (𝟙 (JTSupportedPathChainLabels.ordinals W z M S u hs))
  (Category.id_comp _) (Functor.whiskerLeft (b W z M S u hs) c)
  (parameterLeft_square (b W z M S u hs) px py c hc)

private def pathMap_parameter := identity_parameter
  (K := b W z M S u hs ⋙ JTParametrizedTargetFamilyComparison.degrees M)
  (b W z M S u hs ⋙ X) (b W z M S u hs ⋙ Y)
  (parameterLeft (b W z M S u hs) px)
  (parameterLeft (b W z M S u hs) py) (alpha W z M S u hs)
  (Functor.whiskerLeft (b W z M S u hs) c)
  (parameterLeft_square (b W z M S u hs) px py c hc)

variable (pi : X ⟶ Z)

private def pathProjection := JTSupportedPathWhiskeredGraph.toOld W z M S u hs px ≫
  Functor.whiskerLeft (b W z M S u hs) pi

private def pathProjection_trivial
    (hpi : ∀ i, trivialFibrations SSet.{0} (pi.app i))
    (p : JTSupportedPathChainLabels.Index W z M S u hs) :=
  composite_trivial (K := b W z M S u hs ⋙
    JTParametrizedTargetFamilyComparison.degrees M) (b W z M S u hs ⋙ X) (b W z M S u hs ⋙ Z)
    (parameterLeft (b W z M S u hs) px) (alpha W z M S u hs)
    (Functor.whiskerLeft (b W z M S u hs) pi)
    (JTSupportedPathChainLabels.toOldCoefficient_surjective W z M S u hs)
    (fun q ↦ hpi ((b W z M S u hs).obj q)) p

private def pathProjection_square (pj : Y ⟶ T) (d : Z ⟶ T) (hd : c ≫ pj = pi ≫ d) :=
  composite_square (b W z M S u hs) c pi pj d hd
    (JTSupportedPathWhiskeredGraph.toOld W z M S u hs px)
    (JTSupportedPathWhiskeredGraph.toOld W z M S u hs py)
    (pathMap W z M S u hs px py c hc) (pathMap_toOld W z M S u hs px py c hc)

end Factories

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels F j
private abbrev S := JTSharedInsertionCoarseMiddleSupport.supports F j
private abbrev u := JTSharedInsertionCoarseMiddleSupport.inclusion F j
private abbrev hs := JTSharedInsertionCoarseMiddleSupport.coefficient_onSupport F j

private def actualParameterSquare : ParameterEquation
    (K := JTParametrizedTargetFamilyComparison.degrees (M F j))
    (JTSharedInsertionOldGraph.parameter F j) (JTSharedInsertionCoarseGraph.parameter F j)
    (JTSharedInsertionCoarseGraphComparison.map F j) :=
  JTSharedInsertionCoarseGraphComparison.map_parameter F j

/-- The actual supported path and both complete chain choices. -/
abbrev Index := JTSharedInsertionCoarseSupportedLabels.Index F j

/-- Retain the SAME original shared insertion choices. -/
abbrev toChoices := JTSharedInsertionCoarseSupportedLabels.toChoices F j

/-- The entire final supported coefficient ordinal. -/
abbrev ordinals := JTSharedInsertionCoarseSupportedLabels.ordinals F j

/-- Its existing surjective coordinate to the original shared coefficient. -/
abbrev toOldCoefficient := JTSharedInsertionCoarseSupportedLabels.toOldCoefficient F j

/-- Every old graph assignment and every compatible supported coefficient lift. -/
abbrev graph := JTSupportedPathWhiskeredGraph.graph W (z j)
  (M F j) (S F j) (u F j) (hs F j) (JTSharedInsertionOldGraph.parameter F j)

/-- Forget only the final supported coefficient lift, keeping the whole old graph. -/
abbrev toOld := JTSupportedPathWhiskeredGraph.toOld W (z j)
  (M F j) (S F j) (u F j) (hs F j) (JTSharedInsertionOldGraph.parameter F j)

/-- The full lifted coefficient parameter, with every simplicial degree retained. -/
abbrev parameter := JTSupportedPathWhiskeredGraph.parameter W (z j)
  (M F j) (S F j) (u F j) (hs F j) (JTSharedInsertionOldGraph.parameter F j)

/-- The whole original old native/time product over the unchanged insertion choices. -/
def projection := pathProjection W (z j) (M F j) (S F j) (u F j) (hs F j)
  (JTSharedInsertionOldGraph.parameter F j) (JTSharedInsertionOldGraph.projection F j)

/-- The GIVEN lifted parameter projects to the exact original old graph parameter. -/
def parameter_old := JTSupportedPathWhiskeredGraph.parameter_old W (z j)
  (M F j) (S F j) (u F j) (hs F j) (JTSharedInsertionOldGraph.parameter F j)

/-- Map all assignments into the existing actual coarse supported path graph. -/
def toPathGraph := pathMap W (z j) (M F j) (S F j) (u F j) (hs F j)
  (JTSharedInsertionOldGraph.parameter F j) (JTSharedInsertionCoarseGraph.parameter F j)
  (JTSharedInsertionCoarseGraphComparison.map F j)
  (actualParameterSquare F j)

/-- The complete underlying graph square holds on all supported choices. -/
def toPathGraph_toOld := pathMap_toOld W (z j) (M F j) (S F j) (u F j) (hs F j)
  (JTSharedInsertionOldGraph.parameter F j) (JTSharedInsertionCoarseGraph.parameter F j)
  (JTSharedInsertionCoarseGraphComparison.map F j)
  (actualParameterSquare F j)

/-- The comparison preserves the entire final parameter, not just its old projection. -/
def toPathGraph_parameter := pathMap_parameter W (z j) (M F j) (S F j) (u F j) (hs F j)
  (JTSharedInsertionOldGraph.parameter F j) (JTSharedInsertionCoarseGraph.parameter F j)
  (JTSharedInsertionCoarseGraphComparison.map F j)
  (actualParameterSquare F j)

/-- The complete native/time square, before postcomposing with the fixed target Q. -/
def projection_square := pathProjection_square W (z j) (M F j) (S F j) (u F j) (hs F j)
  (JTSharedInsertionOldGraph.parameter F j) (JTSharedInsertionCoarseGraph.parameter F j)
  (JTSharedInsertionCoarseGraphComparison.map F j)
  (actualParameterSquare F j)
  (JTSharedInsertionOldGraph.projection F j) (JTSharedInsertionCoarseGraph.projection F j)
  (JTSharedInsertionCoarseGraphComparison.productMap F j)
  (JTSharedInsertionCoarseGraphComparison.map_projection F j)

/-- The whole old product projection is a trivial fibration, without selecting any lift. -/
def projection_trivialFibration (p : Index F j) := pathProjection_trivial
  W (z j) (M F j) (S F j) (u F j) (hs F j)
  (JTSharedInsertionOldGraph.parameter F j) (JTSharedInsertionOldGraph.projection F j)
  (JTSharedInsertionOldGraph.projection_trivialFibration F j) p

end
end DaggerModels.PartII.JTSharedInsertionSupportedComparisonGraph
