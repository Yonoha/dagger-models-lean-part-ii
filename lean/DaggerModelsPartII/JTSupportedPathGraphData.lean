import DaggerModelsPartII.JTSupportedPathChainLabels
import DaggerModelsPartII.JTGraphCoveredLabelEvaluation
import DaggerModelsPartII.JTGraphCoveredPresentationWeak

/-! Exact supported graph data and its full lifts along higher contraction chains. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathGraphData

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open JTPointTargetEvaluationCone (pointTarget)
open JTOrderedLabelJointInsertion (toPointNatural)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (time S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)

/-- The entire original native necklace, with its unchanged full groupoid time. -/
abbrev nativePrism := JTJointRelativeParameters.withTime (pointTarget W z).map J time
  (Over.lift (codes L) (toPointNatural (codes L)))
  (JTTargetIntervalOverMapping.whole (pointTarget W z).code)

/-- An exact original graph and its natural factor through the prescribed support. -/
structure GraphData where
  domain : I ⥤ SSet.{0}
  projection : domain ⟶ nativePrism W z L time
  parameter : domain ⟶ K W z L ⋙ J
  supportParameter : domain ⟶ S ⋙ J
  support_fac : supportParameter ≫ Functor.whiskerRight u J = parameter

variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (G : GraphData W z L time S u)

/-- The ordinary decorated chain index of every higher contraction choice. -/
abbrev Index := JTSupportedPathChainLabels.Index W z L S u hs

/-- Retain the original diagram index through the full path and chain covers. -/
abbrev base : Index W z L S u hs ⥤ I :=
  JTSupportedPathChainLabels.toOriginal W z L S u hs

/-- The complete changing decorated labels on those chains. -/
abbrev labels := JTSupportedPathChainLabels.labels W z L S u hs

/-- The original full time is pulled back without replacement. -/
abbrev oldTime : Index W z L S u hs ⥤ SimplexCategory := base W z L S u hs ⋙ time

private abbrev α : JTSupportedPathChainLabels.ordinals W z L S u hs ⟶
    base W z L S u hs ⋙ K W z L :=
  JTSupportedPathChainLabels.toOldCoefficient W z L S u hs
private abbrev X := base W z L S u hs ⋙ G.domain
private abbrev p : X W z L time S u hs G ⟶
    (base W z L S u hs ⋙ K W z L) ⋙ J :=
  Functor.whiskerLeft (base W z L S u hs) G.parameter

/-- All compatible coefficient-chain lifts of the original full graph. -/
abbrev graph : Index W z L S u hs ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover
    (k := base W z L S u hs ⋙ K W z L)
    (m := JTSupportedPathChainLabels.ordinals W z L S u hs)
    (X W z L time S u hs G)
    (p W z L time S u hs G) (α W z L S u hs)

/-- Recover the original complete graph, not just its vertices or one time slice. -/
abbrev projection : graph W z L time S u hs G ⟶ X W z L time S u hs G :=
  JTPrismChainGraphCover.projection
    (k := base W z L S u hs ⋙ K W z L)
    (m := JTSupportedPathChainLabels.ordinals W z L S u hs)
    (X W z L time S u hs G)
    (p W z L time S u hs G) (α W z L S u hs)

/-- The exact groupoid parameter in the final path-chain coefficient ordinal. -/
abbrev parameter : graph W z L time S u hs G ⟶
    JTSupportedPathChainLabels.ordinals W z L S u hs ⋙ J :=
  JTPrismChainGraphCover.parameter
    (k := base W z L S u hs ⋙ K W z L)
    (m := JTSupportedPathChainLabels.ordinals W z L S u hs)
    (X W z L time S u hs G)
    (p W z L time S u hs G) (α W z L S u hs)

/-- The full original support coordinate is retained through the graph cover. -/
abbrev supportParameter : graph W z L time S u hs G ⟶
    base W z L S u hs ⋙ S ⋙ J :=
  projection W z L time S u hs G ≫
    Functor.whiskerLeft (base W z L S u hs) G.supportParameter

/-- The lifted groupoid parameter satisfies the exact old-support square. -/
theorem parameter_support :
    parameter W z L time S u hs G ≫ Functor.whiskerRight (α W z L S u hs) J =
      supportParameter W z L time S u hs G ≫
        Functor.whiskerLeft (base W z L S u hs) (Functor.whiskerRight u J) := by
  rw [JTPrismChainGraphCover.parameter_projection]
  apply NatTrans.ext
  funext a
  change (projection W z L time S u hs G).app a ≫ G.parameter.app _ =
    ((projection W z L time S u hs G).app a ≫ G.supportParameter.app _) ≫ J.map _
  rw [Category.assoc]
  exact congrArg ((projection W z L time S u hs G).app a ≫ ·)
    (NatTrans.congr_app G.support_fac ((base W z L S u hs).obj a)).symm

/-- Surjectivity retains an actual trivial fibration over the whole old graph. -/
theorem projection_trivialFibration (a : Index W z L S u hs) :
    trivialFibrations SSet.{0} ((projection W z L time S u hs G).app a) :=
  JTPrismChainGraphCover.projection_trivialFibration (X W z L time S u hs G)
    (p W z L time S u hs G) (α W z L S u hs)
    (JTSupportedPathChainLabels.toOldCoefficient_surjective W z L S u hs) a

end
end DaggerModels.PartII.JTSupportedPathGraphData
