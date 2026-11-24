import DaggerModelsPartII.JTActualJointChainSideLabels
import DaggerModelsPartII.JTActualJointSideWhiskerNative
import DaggerModelsPartII.JTActualJointSideParameterTransport
import DaggerModelsPartII.JTPrismChainGraphCover

/-! Original coarse side parameters and their full chain graph covers. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointChainSideGraph

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

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChoiceChainGraph.Index F j
private abbrev choice := JTActualJointChoiceChainGraph.base F j
private abbrev marked := choice F j ⋙ JTActualJointChoiceCover.projection F j
private abbrev original := marked F j ⋙ JTExactlyMarkedSourceDiagram.base F j
private abbrev old (p : I F j) := (original F j).obj p
private abbrev v (p : I F j) := ((marked F j).obj p).2.val
private abbrev hv (p : I F j) := ((marked F j).obj p).2.property
private abbrev oldArrow {p q : I F j} (f : p ⟶ q) := (original F j).map f

private theorem cut_map {p q : I F j} (f : p ⟶ q) :
    orderMap ((codes L).map (oldArrow F j f)).map (v F j p) = v F j q :=
  JTExactlyMarkedSourceDiagram.cut_map F j ((marked F j).map f)

/-- The original coefficient degrees and time on each full chain. -/
abbrev oldDegrees : I F j ⥤ SimplexCategory :=
  original F j ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

/-- The original groupoid time, retained before lifting the coefficient. -/
abbrev oldTime : I F j ⥤ SimplexCategory := original F j ⋙ time

/-- The complete corrected native codes on the left. -/
abbrev leftCodes := codes (JTActualJointChainSideLabels.leftLabels F j)

/-- The complete corrected native codes on the right. -/
abbrev rightCodes := codes (JTActualJointChainSideLabels.rightLabels F j)

/-- The corrected left native code and original time form a complete graph domain. -/
abbrev leftX : I F j ⥤ SSet.{0} :=
  (((leftCodes F j) ⋙ NecklaceCode.simplicialFunctor).prod'
    ((oldTime F j) ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}

/-- The corrected right native code with the same original time. -/
abbrev rightX : I F j ⥤ SSet.{0} :=
  (((rightCodes F j) ⋙ NecklaceCode.simplicialFunctor).prod'
    ((oldTime F j) ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}

set_option maxHeartbeats 850000 in
/-- Collapse the added ending edge to the old cut endpoint and retain the old cut. -/
def leftCoarseParameter : leftX F j ⟶ oldDegrees F j ⋙ J where
  app p := JTJointSideWhisker.appendParameter
    (JTActualJointCutPrism.leftParameter F (old F j p) (v F j p))
  naturality p q f := by
    exact JTActualJointSideParameterTransport.left_map F (oldArrow F j f)
      (v F j p) (v F j q) (cut_map F j f)

set_option maxHeartbeats 850000 in
/-- Collapse the added starting edge to the old cut endpoint. -/
def rightCoarseParameter : rightX F j ⟶ oldDegrees F j ⋙ J where
  app p := JTJointSideWhisker.prependParameter
    (JTActualJointCutPrism.rightParameter F (old F j p) (v F j p))
  naturality p q f := by
    exact JTActualJointSideParameterTransport.right_map F (oldArrow F j f)
      (v F j p) (v F j q) (cut_map F j f)

/-- All compatible coefficient lifts of the coarse left graph on every chain. -/
abbrev leftGraph : I F j ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (leftX F j) (leftCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- All compatible coefficient lifts of the coarse right graph on every chain. -/
abbrev rightGraph : I F j ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (rightX F j) (rightCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- Projection from the left graph cover to its exact corrected native domain. -/
abbrev leftProjection : leftGraph F j ⟶ leftX F j :=
  JTPrismChainGraphCover.projection (leftX F j) (leftCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- Projection from the right graph cover to its exact corrected native domain. -/
abbrev rightProjection : rightGraph F j ⟶ rightX F j :=
  JTPrismChainGraphCover.projection (rightX F j) (rightCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- The left lifted coefficient has the actual full-chain ordinal. -/
abbrev leftParameter : leftGraph F j ⟶
    JTActualJointChoiceChainGraph.ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter (leftX F j) (leftCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- The right lifted coefficient has the same full-chain ordinal. -/
abbrev rightParameter : rightGraph F j ⟶
    JTActualJointChoiceChainGraph.ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter (rightX F j) (rightCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- The left lift projects to the unchanged coarse old coefficient parameter. -/
theorem leftParameter_projection :
    leftParameter F j ≫ Functor.whiskerRight
      (JTActualJointChoiceChainGraph.toOriginal F j) J =
      leftProjection F j ≫ leftCoarseParameter F j :=
  JTPrismChainGraphCover.parameter_projection (leftX F j) (leftCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- The right lift projects to the unchanged coarse old coefficient parameter. -/
theorem rightParameter_projection :
    rightParameter F j ≫ Functor.whiskerRight
      (JTActualJointChoiceChainGraph.toOriginal F j) J =
      rightProjection F j ≫ rightCoarseParameter F j :=
  JTPrismChainGraphCover.parameter_projection (rightX F j) (rightCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

private theorem collapse_natural {p q : I F j} (f : p ⟶ q) :
    (codes L).map (oldArrow F j f) ≫ F.collapse.app (old F j q) =
      F.collapse.app (old F j p) :=
  (F.collapse.naturality (oldArrow F j f)).trans (Category.comp_id _)

private theorem leftNative_eq {S : NecklaceCode} {f g : S ⟶ Q.code}
    (w : Fin (S.len + 1)) (hf : orderMap f.map w = j.val)
    (hg : orderMap g.map w = j.val) (h : f = g) :
    JTActualJointSideWhiskerNative.leftNative Q j f w hf =
      JTActualJointSideWhiskerNative.leftNative Q j g w hg := by
  subst g
  rfl

private theorem rightNative_eq {S : NecklaceCode} {f g : S ⟶ Q.code}
    (w : Fin (S.len + 1)) (hf : orderMap f.map w = j.val)
    (hg : orderMap g.map w = j.val) (h : f = g) :
    JTActualJointSideWhiskerNative.rightNative Q j f w hf =
      JTActualJointSideWhiskerNative.rightNative Q j g w hg := by
  subst g
  rfl

/-- The literal left native collapses commute with every complete chain arrow. -/
def leftNative : leftCodes F j ⟶
    (Functor.const (I F j)).obj (JTActualJointMarkedEvaluation.left Q j).code where
  app p := JTActualJointSideWhiskerNative.leftNative Q j
    (F.collapse.app (old F j p)) (v F j p) (hv F j p)
  naturality p q f := by
    let g := (codes L).map (oldArrow F j f)
    let f' := F.collapse.app (old F j q)
    have hc := JTActualJointSideNativeTransport.leftNative_comp Q j g f'
      (v F j p) (v F j q) (cut_map F j f) (hv F j q)
    change JTActualJointSideNativeTransport.leftTransport g
        (v F j p) (v F j q) (cut_map F j f) ≫
        JTActualJointSideWhiskerNative.leftNative Q j f' (v F j q) (hv F j q) =
      JTActualJointSideWhiskerNative.leftNative Q j
        (F.collapse.app (old F j p)) (v F j p) (hv F j p) ≫ 𝟙 _
    rw [Category.comp_id, hc]
    exact leftNative_eq j (v F j p) _ _ (collapse_natural F j f)

/-- The literal right native collapses commute with every chain arrow. -/
def rightNative : rightCodes F j ⟶
    (Functor.const (I F j)).obj (JTActualJointMarkedEvaluation.right Q j).code where
  app p := JTActualJointSideWhiskerNative.rightNative Q j
    (F.collapse.app (old F j p)) (v F j p) (hv F j p)
  naturality p q f := by
    let g := (codes L).map (oldArrow F j f)
    let f' := F.collapse.app (old F j q)
    have hc := JTActualJointSideNativeTransport.rightNative_comp Q j g f'
      (v F j p) (v F j q) (cut_map F j f) (hv F j q)
    change JTActualJointSideNativeTransport.rightTransport g
        (v F j p) (v F j q) (cut_map F j f) ≫
        JTActualJointSideWhiskerNative.rightNative Q j f' (v F j q) (hv F j q) =
      JTActualJointSideWhiskerNative.rightNative Q j
        (F.collapse.app (old F j p)) (v F j p) (hv F j p) ≫ 𝟙 _
    rw [Category.comp_id, hc]
    exact rightNative_eq j (v F j p) _ _ (collapse_natural F j f)

/-- Actual left native diagrams in the over category of the unchanged target code. -/
def leftOver : I F j ⥤ Over (JTActualJointMarkedEvaluation.left Q j).code :=
  Over.lift (leftCodes F j) (leftNative F j)

/-- Actual right native diagrams over the unchanged target code. -/
def rightOver : I F j ⥤ Over (JTActualJointMarkedEvaluation.right Q j).code :=
  Over.lift (rightCodes F j) (rightNative F j)


/-- The coarse left parameter retains the old parameter on the entire cut. -/
theorem leftCoarse_interior (p : I F j) :
    (wedgeιLeft (cutLeft ((codes L).obj (old F j p)) (v F j p)) (single 1) ⊗ₘ
      𝟙 (J.obj ((oldTime F j).obj p))) ≫ (leftCoarseParameter F j).app p =
    JTActualJointCutPrism.leftParameter F (old F j p) (v F j p) :=
  JTJointSideWhisker.appendParameter_interior _

/-- The coarse right parameter retains the old parameter on the entire cut. -/
theorem rightCoarse_interior (p : I F j) :
    (wedgeιRight (single 1) (cutRight ((codes L).obj (old F j p)) (v F j p)) ⊗ₘ
      𝟙 (J.obj ((oldTime F j).obj p))) ≫ (rightCoarseParameter F j).app p =
    JTActualJointCutPrism.rightParameter F (old F j p) (v F j p) :=
  JTJointSideWhisker.prependParameter_interior _

/-- The appended edge repeats the original source-vertex parameter through all time. -/
theorem leftCoarse_whisker (p : I F j) :
    (wedgeιRight (cutLeft ((codes L).obj (old F j p)) (v F j p)) (single 1) ⊗ₘ
      𝟙 (J.obj ((oldTime F j).obj p))) ≫ (leftCoarseParameter F j).app p =
    JTJointSideWhisker.edgeParameter
      (JTActualSourceJointSupport.timeParameter F (old F j p) (v F j p)) := by
  change (wedgeιRight _ _ ⊗ₘ 𝟙 _) ≫
    JTJointSideWhisker.appendParameter
      (JTActualJointCutPrism.leftParameter F (old F j p) (v F j p)) = _
  rw [JTJointSideWhisker.appendParameter, JTComposedPrismLabels.parameter_right]
  congr 1
  unfold JTActualJointCutPrism.leftParameter JTActualSourceJointSupport.timeParameter
  change ((pointAt (cutLeft ((codes L).obj (old F j p)) (v F j p))
      (ULift.up (Fin.last _)) ⊗ₘ 𝟙 _) ≫
      ((cutLeftι ((codes L).obj (old F j p)) (v F j p) ⊗ₘ 𝟙 _) ≫
        F.parameter (old F j p))) = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  have h : pointAt (cutLeft ((codes L).obj (old F j p)) (v F j p))
      (ULift.up (Fin.last _)) ≫ cutLeftι ((codes L).obj (old F j p)) (v F j p) =
    pointAt ((codes L).obj (old F j p)) (ULift.up (v F j p)) :=
    DaggerOriginalProductGadget.intervalPoint_last _ 0 (v F j p) (Fin.zero_le _)
  rw [h]

/-- The prepended edge repeats the same original source-vertex parameter. -/
theorem rightCoarse_whisker (p : I F j) :
    (wedgeιLeft (single 1) (cutRight ((codes L).obj (old F j p)) (v F j p)) ⊗ₘ
      𝟙 (J.obj ((oldTime F j).obj p))) ≫ (rightCoarseParameter F j).app p =
    JTJointSideWhisker.edgeParameter
      (JTActualSourceJointSupport.timeParameter F (old F j p) (v F j p)) := by
  change (wedgeιLeft _ _ ⊗ₘ 𝟙 _) ≫
    JTJointSideWhisker.prependParameter
      (JTActualJointCutPrism.rightParameter F (old F j p) (v F j p)) = _
  rw [JTJointSideWhisker.prependParameter, JTComposedPrismLabels.parameter_left]
  congr 1
  unfold JTActualJointCutPrism.rightParameter JTActualSourceJointSupport.timeParameter
  change ((pointAt (cutRight ((codes L).obj (old F j p)) (v F j p))
      (ULift.up 0) ⊗ₘ 𝟙 _) ≫
      ((cutRightι ((codes L).obj (old F j p)) (v F j p) ⊗ₘ 𝟙 _) ≫
        F.parameter (old F j p))) = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  have h : pointAt (cutRight ((codes L).obj (old F j p)) (v F j p))
      (ULift.up 0) ≫ cutRightι ((codes L).obj (old F j p)) (v F j p) =
    pointAt ((codes L).obj (old F j p)) (ULift.up (v F j p)) :=
    DaggerOriginalProductGadget.intervalPoint_first _ (v F j p)
      (Fin.last _) (Fin.le_last _)
  rw [h]


/-- Each left graph projection is a trivial fibration of simplicial sets. -/
theorem leftProjection_trivialFibration (p : I F j) :
    HomotopicalAlgebra.trivialFibrations SSet.{0} ((leftProjection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration
    (leftX F j) (leftCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)
    (JTActualJointChoiceChainGraph.toOriginal_surjective F j) p

/-- Each right graph projection has the same componentwise lifting property. -/
theorem rightProjection_trivialFibration (p : I F j) :
    HomotopicalAlgebra.trivialFibrations SSet.{0} ((rightProjection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration
    (rightX F j) (rightCoarseParameter F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)
    (JTActualJointChoiceChainGraph.toOriginal_surjective F j) p

end
end DaggerModels.PartII.JTActualJointChainSideGraph
