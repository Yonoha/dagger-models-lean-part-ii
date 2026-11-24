import DaggerModelsPartII.JTOrderedLabelPaddingPrismChains
import DaggerModelsPartII.JTPrismChainGraphCover
import DaggerModelsPartII.JTJointRelativeGraphFamily

/-! Cover the original graph by every lifted coefficient on a chosen prism chain. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismChainGraphs

open JTOrderedLabelPaddingPrismChains (base oldLabels realizedLabels toOriginal toRealized)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family codes)
open JTRealizedLabelEndpoints (orderedLabel)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time)

private abbrev b := boundaryPoint W x y
private abbrev I := JTOrderedLabelPaddingPrismChains.Index W (b (W := W) (x := x) (y := y)) L
private abbrev toBase :=
  base W (b (W := W) (x := x) (y := y)) L ⋙
    JTOrderedLabelPaddingPrismSliceArrow.originalBase W (b (W := W) (x := x) (y := y)) L
private abbrev old (p : I (L := L)) := (oldLabels W (b (W := W) (x := x) (y := y)) L).obj p
private abbrev new (p : I (L := L)) := (realizedLabels W (b (W := W) (x := x) (y := y)) L).obj p
private abbrev T (p : I (L := L)) := OrderedLabelElements.necklace W (b (W := W) (x := x) (y := y))
  (old p)
private abbrev d (i : OrderedLabelElements.Index W (b (W := W) (x := x) (y := y))) :=
  OrderedLabelElements.degree W (b (W := W) (x := x) (y := y)) i
private abbrev label (i : OrderedLabelElements.Index W (b (W := W) (x := x) (y := y))) :=
  OrderedLabelElements.label W (b (W := W) (x := x) (y := y)) i

abbrev original := F.precomp (toBase (L := L))
abbrev X := JTJointRelativeParameters.withTime Q.map J (toBase (L := L) ⋙ time)
  (JTJointRelativeGraphFamily.native (original F)) (JTTargetIntervalOverMapping.whole Q.code)
private abbrev parameter₀ := JTJointRelativeGraphFamily.originalParameter (original F)
private abbrev α := toOriginal W (b (W := W) (x := x) (y := y)) L
private abbrev β := toRealized W (b (W := W) (x := x) (y := y)) L

/-- Adjoin every lifted chain coefficient at each vertex of the original graph. -/
abbrev graphCover : I (L := L) ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (X F) (parameter₀ F) α

/-- Recover the original graph from the covered graph. -/
abbrev projection : graphCover F ⟶ X F :=
  JTPrismChainGraphCover.projection (X F) (parameter₀ F) α

/-- The parameter in the realized label uses the full chosen chain. -/
abbrev realizedParameter :=
  JTPrismChainGraphCover.parameter (X F) (parameter₀ F) α ≫ Functor.whiskerRight β J

/-- Every component of the original graph is covered by a trivial fibration. -/
theorem projection_trivialFibration (p : I (L := L)) :
    trivialFibrations SSet.{0} ((projection F).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration (X F) (parameter₀ F) α
    (JTOrderedLabelPaddingPrismChains.toOriginal_surjective W (b (W := W) (x := x) (y := y)) L) p

abbrev horizontal (p : I (L := L)) :=
  (projection F).app p ≫ fst (T p).toSSet (J.obj ((toBase (L := L) ⋙ time).obj p))

/-- The entire covered graph evaluates in the same raw target, at every lifted time. -/
theorem raw (p : I (L := L)) :
    lift (horizontal F p) ((realizedParameter F).app p) ≫
      realizedLabel (T p).toSSet W (d (new p))
        (orderedLabel W x y (T p) (d (new p)) (label (new p))) =
    (horizontal F p) ≫ ((original F).collapse.app p).map ≫ Q.map := by
  let τ := JTPrismChainGraphCover.parameter (X F) (parameter₀ F) α
  have h := JTOrderedLabelPaddingPrismChains.labels_restrict W (b (W := W) (x := x) (y := y)) L p
  have hv := NatTrans.congr_app
    (JTPrismChainGraphCover.parameter_projection (X F) (parameter₀ F) α) p
  change τ.app p ≫ J.map (α.app p) = (projection F).app p ≫ (original F).parameter p at hv
  change lift (horizontal F p) (τ.app p ≫ J.map (β.app p)) ≫ _ = _
  refine (JTPrismChainGraphCover.realize_on_common_chain
    (α.app p) (β.app p) (horizontal F p) (τ.app p) (label (old p)) (label (new p)) h).trans ?_
  rw [hv]
  have ht := JTParametrizedTargetFamilies.rawProduct (original F) p
  change lift ((projection F).app p ≫ fst _ _)
       ((projection F).app p ≫ (original F).parameter p) ≫ _ = _
  rw [← CartesianMonoidalCategory.comp_lift, Category.assoc]
  exact (congrArg ((projection F).app p ≫ ·) ht).trans
    (Category.assoc _ _ _).symm

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismChainGraphs
