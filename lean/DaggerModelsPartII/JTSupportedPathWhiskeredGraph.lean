import DaggerModelsPartII.JTSupportedPathWhiskeredDiagram
import DaggerModelsPartII.JTPrismChainGraphCover

/-!
# Full graph for the supported path with varying surrounding labels

Reuse: `JTSupportedPathChainLabels.toOldCoefficient_surjective`,
`JTPrismChainGraphCover.parameter_projection` and
`JTPrismChainGraphCover.projection_trivialFibration`. The native code of the
path label is the original three-piece code after reindexing, so the old
graph is reindexed directly; no full-product parameter is inferred.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathWhiskeredGraph

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open TripleBeadEndpointLabel (firstRestriction lastRestriction)
open OrderedNecklaceVertexPoints (boundaryPoint zeroPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (P R : I ⥤ NecklaceCode)
variable (A : JTSupportedPathWhiskeredDiagram.Surroundings W x z y L P R)

private abbrev Index := JTSupportedPathChainLabels.Index W z L S u hs
private abbrev base := JTSupportedPathChainLabels.toOriginal W z L S u hs
private abbrev degree := JTSupportedPathChainLabels.ordinals W z L S u hs
private abbrev α := JTSupportedPathChainLabels.toOldCoefficient W z L S u hs

/-- The original three-piece full coefficient before the supported path. -/
def oldData (a : I) : JTThreePieceLabelOperators.Data W
    (P.obj a) ((codes L).obj a) (R.obj a) ((K W z L).obj a) x y where
  left := A.left a
  middle := JTSupportedOrderedCoefficientChoices.old W z L a
  right := A.right a
  left_join := by
    rw [A.inner_left a]
    exact (JTOrderedLabelBinaryGlue.coefficient_first W z z
      ((codes L).obj a) ((K W z L).obj a)
      (OrderedLabelElements.label W (boundaryPoint W z z) (L.obj a))).symm
  right_join := by
    rw [A.inner_right a]
    exact JTOrderedLabelBinaryGlue.coefficient_last W z z
      ((codes L).obj a) ((K W z L).obj a)
      (OrderedLabelElements.label W (boundaryPoint W z z) (L.obj a))
  first := A.global_first a
  last := A.global_last a

/-- The unchanged original three-piece decorated family. -/
def oldFamily : JTVariableMiddleWhiskeredDiagram.Family
    (W := W) (x := x) (y := y) P (codes L) R (K W z L) where
  data a := oldData W x z y L P R A a
  left_nat g := A.left_nat g
  middle_nat g := JTSupportedOrderedCoefficientChoices.old_map W z L g
  right_nat g := A.right_nat g

abbrev oldLabels : I ⥤ DecoratedNecklaceHomDiagram.Index W x y :=
  (oldFamily W x z y L P R A).labels

abbrev pathLabels : Index W z L S u hs ⥤
    DecoratedNecklaceHomDiagram.Index W x y :=
  JTSupportedPathWhiskeredDiagram.labels W x z y L S u hs P R A

/-- The full three-piece native necklace is unchanged by the path and is
reindexed along its chain cover, including every native operator. -/
theorem code_reindex : codes (pathLabels W x z y L S u hs P R A) =
    base W z L S u hs ⋙ codes (oldLabels W x z y L P R A) := by
  rfl

variable (time : I ⥤ SimplexCategory)

/-- The complete original three-piece native product with its independent
unchanged time simplex. -/
abbrev oldProduct : I ⥤ SSet.{0} :=
  ((codes (oldLabels W x z y L P R A) ⋙ NecklaceCode.simplicialFunctor).prod'
    (time ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}

/-- The literal new product named from the supported path labels. -/
abbrev newProduct : Index W z L S u hs ⥤ SSet.{0} :=
  ((codes (pathLabels W x z y L S u hs P R A) ⋙
      NecklaceCode.simplicialFunctor).prod'
    ((base W z L S u hs ⋙ time) ⋙ J)) ⋙
      MonoidalCategory.tensor SSet.{0}

theorem newProduct_eq : newProduct W x z y L S u hs P R A time =
    base W z L S u hs ⋙ oldProduct W x z y L P R A time := by
  rw [newProduct, oldProduct, code_reindex]
  rfl

variable {Y : I ⥤ SSet.{0}}
variable (oldπ : Y ⟶ oldProduct W x z y L P R A time)
variable (oldθ : Y ⟶ (K W z L) ⋙ J)

/-- Retain the entire old graph at each final path-chain simplex. -/
abbrev oldGraph : Index W z L S u hs ⥤ SSet.{0} :=
  base W z L S u hs ⋙ Y

abbrev coarseParameter : oldGraph (Y := Y) W z L S u hs ⟶
    (base W z L S u hs ⋙ K W z L) ⋙ J :=
  Functor.whiskerLeft (base W z L S u hs) oldθ

/-- All coefficient lifts of the unchanged full old graph. -/
abbrev graph : Index W z L S u hs ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (oldGraph (Y := Y) W z L S u hs)
    (coarseParameter W z L S u hs oldθ) (α W z L S u hs)

/-- Projection back to the old whole graph. -/
abbrev toOld : graph W z L S u hs oldθ ⟶
    oldGraph (Y := Y) W z L S u hs :=
  JTPrismChainGraphCover.projection (oldGraph (Y := Y) W z L S u hs)
    (coarseParameter W z L S u hs oldθ) (α W z L S u hs)

/-- Projection to the new whole native product, identified with the old
product after reindexing. -/
abbrev projection : graph W z L S u hs oldθ ⟶
    base W z L S u hs ⋙ oldProduct W x z y L P R A time :=
  toOld W z L S u hs oldθ ≫
    Functor.whiskerLeft (base W z L S u hs) oldπ

/-- The same projection typed against the literal new path native product. -/
def projectionNew : graph W z L S u hs oldθ ⟶
    newProduct W x z y L S u hs P R A time :=
  projection W x z y L S u hs P R A time oldπ oldθ ≫
    eqToHom (newProduct_eq W x z y L S u hs P R A time).symm

theorem projectionNew_app (p : Index W z L S u hs) :
    (projectionNew W x z y L S u hs P R A time oldπ oldθ).app p =
      (projection W x z y L S u hs P R A time oldπ oldθ).app p := by
  rfl

/-- The lifted groupoid parameter in the actual path-chain degree. -/
abbrev parameter : graph W z L S u hs oldθ ⟶
    degree W z L S u hs ⋙ J :=
  JTPrismChainGraphCover.parameter (oldGraph (Y := Y) W z L S u hs)
    (coarseParameter W z L S u hs oldθ) (α W z L S u hs)

theorem parameter_old : parameter W z L S u hs oldθ ≫
    Functor.whiskerRight (α W z L S u hs) J =
      toOld W z L S u hs oldθ ≫
        Functor.whiskerLeft (base W z L S u hs) oldθ :=
  JTPrismChainGraphCover.parameter_projection
    (oldGraph (Y := Y) W z L S u hs)
    (coarseParameter W z L S u hs oldθ) (α W z L S u hs)

theorem native_square : projection W x z y L S u hs P R A time oldπ oldθ =
    toOld W z L S u hs oldθ ≫
      Functor.whiskerLeft (base W z L S u hs) oldπ := rfl

/-- Surjective old-degree chains preserve the old graph's componentwise
trivial fibration after reindexing. -/
theorem projection_trivialFibration
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a))
    (p : Index W z L S u hs) :
    trivialFibrations SSet.{0}
      ((projection W x z y L S u hs P R A time oldπ oldθ).app p) :=
  (trivialFibrations SSet.{0}).comp_mem _ _
    (JTPrismChainGraphCover.projection_trivialFibration
      (oldGraph (Y := Y) W z L S u hs) (coarseParameter W z L S u hs oldθ)
      (α W z L S u hs)
      (JTSupportedPathChainLabels.toOldCoefficient_surjective W z L S u hs) p)
    (hπ ((base W z L S u hs).obj p))

end
end DaggerModels.PartII.JTSupportedPathWhiskeredGraph
