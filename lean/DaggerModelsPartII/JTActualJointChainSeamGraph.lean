import DaggerModelsPartII.JTActualJointChainSeamNative
import DaggerModelsPartII.JTPrismChainGraphCover

/-!
The full original-time graph of the actual seam triangle. All lifts through
the composite coefficient projection are retained as a natural graph cover.
No natural section of an ordinal surjection or chain-degree Family is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChainSeamGraph

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTActualJointChainSeamNative (seamFamily original wholeNative oldDegrees coefficientProjection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev toSSet := NecklaceCode.simplicialFunctor.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChainSeamChoices.Index F j
private abbrev natives := codes (seamFamily F j).triangle.labels

/-- The entire original time simplex and every original time operator are retained. -/
abbrev oldTime : I F j ⥤ SimplexCategory := original F j ⋙ time

/-- The whole triangle necklace paired with the complete original time parameter. -/
abbrev X : I F j ⥤ SSet.{0} :=
  (((natives F j) ⋙ toSSet).prod' ((oldTime F j) ⋙ J)) ⋙
    MonoidalCategory.tensor SSet.{0}

private abbrev oldProduct : I F j ⥤ SSet.{0} :=
  (((original F j ⋙ codes L) ⋙ toSSet).prod' ((oldTime F j) ⋙ J)) ⋙
    MonoidalCategory.tensor SSet.{0}

private def oldParameter : oldProduct F j ⟶ oldDegrees F j ⋙ J where
  app p := F.parameter ((original F j).obj p)
  naturality _ _ g := F.parameter_map ((original F j).map g)

/-- The actual whole native reassembly acts with identity on the entire old time. -/
def nativeTimeMap : X F j ⟶ oldProduct F j :=
  Functor.whiskerRight
    (NatTrans.prod' (Functor.whiskerRight (wholeNative F j) toSSet)
      (𝟙 ((oldTime F j) ⋙ J))) (MonoidalCategory.tensor SSet.{0})

/-- The literal original Family parameter after whole native reassembly. -/
def coarseParameter : X F j ⟶ oldDegrees F j ⋙ J :=
  nativeTimeMap F j ≫ oldParameter F j

/-- Every complete native/time prism uses exactly the original parameter. -/
theorem coarseParameter_app (p : I F j) :
    (coarseParameter F j).app p =
      (((wholeNative F j).app p).map ⊗ₘ 𝟙 (J.obj ((oldTime F j).obj p))) ≫
        F.parameter ((original F j).obj p) := rfl

/-- Retain all coefficient lifts to the actual composite full-chain degree. -/
abbrev graph : I F j ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The full graph projection keeps the whole triangle and every old time simplex. -/
abbrev projection : graph F j ⟶ X F j :=
  JTPrismChainGraphCover.projection (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The complete lifted coefficient parameter, natural in all actual operators. -/
abbrev parameter : graph F j ⟶ JTActualJointChainSeamChoices.ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The lifted parameter recovers the exact original whole-prism parameter. -/
theorem parameter_projection :
    parameter F j ≫ Functor.whiskerRight (coefficientProjection F j) J =
      projection F j ≫ coarseParameter F j :=
  JTPrismChainGraphCover.parameter_projection
    (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- Each entire graph cover projects by a trivial fibration. -/
theorem projection_trivialFibration (p : I F j) :
    trivialFibrations SSet.{0} ((projection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration (X F j) (coarseParameter F j)
    (coefficientProjection F j)
    (JTActualJointChainSeamNative.coefficientProjection_surjective F j) p

/-- The full triangle native coordinate of a lifted graph point. -/
abbrev native (p : I F j) :=
  (projection F j).app p ≫ fst (((natives F j).obj p).toSSet)
    (J.obj ((oldTime F j).obj p))

/-- Its unchanged full original time coordinate. -/
abbrev clock (p : I F j) :=
  (projection F j).app p ≫ snd (((natives F j).obj p).toSSet)
    (J.obj ((oldTime F j).obj p))

/-- The two coordinates recover the entire graph projection. -/
theorem native_clock (p : I F j) :
    lift (native F j p) (clock F j p) = (projection F j).app p :=
  lift_comp_fst_snd _

/-- The exact original parameter identity at every whole graph component. -/
theorem parameter_projection_app (p : I F j) :
    (parameter F j).app p ≫ J.map ((coefficientProjection F j).app p) =
      (projection F j).app p ≫
        ((((wholeNative F j).app p).map ⊗ₘ 𝟙 (J.obj ((oldTime F j).obj p))) ≫
          F.parameter ((original F j).obj p)) := by
  have h := congrArg (fun η : graph F j ⟶ oldDegrees F j ⋙ J ↦ η.app p)
    (parameter_projection F j)
  change (parameter F j).app p ≫ J.map ((coefficientProjection F j).app p) =
    (projection F j).app p ≫ (coarseParameter F j).app p at h
  rw [coarseParameter_app] at h
  exact h

end
end DaggerModels.PartII.JTActualJointChainSeamGraph
