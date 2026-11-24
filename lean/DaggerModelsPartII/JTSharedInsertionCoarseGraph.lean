import DaggerModelsPartII.JTSharedInsertionCoarseNative
import DaggerModelsPartII.JTSharedInsertionPhaseGraph
import DaggerModelsPartII.JTJointRelativeGraphFamily

/-!
# Every original-time coefficient lift of the ACTUAL coarse label

The exact coarse native assembly is followed by the EXISTING original Family
parameter. Keep ALL lifts through the original shared coefficient projection,
without choosing a section. The entire original time is separate from the tuple
clock. No coarse raw equation or evaluation is assumed or asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

private def parameterAlong {A I : Type} [SmallCategory A] [SmallCategory I]
    {W : Source} {x y : Vertex W}
    {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
    (F : Family Q L time) (O : I ⥤ A) (N : I ⥤ NecklaceCode) (n : N ⟶ O ⋙ codes L) :
    JTGraphCoveredProductInterface.product N (O ⋙ time) ⟶
      (O ⋙ JTJointRelativeGraphFamily.coefficient (L := L)) ⋙ J :=
  JTSharedInsertionPhaseGraph.reindexedProductMap O n time ≫
    Functor.whiskerLeft O
      ((JTGraphCoveredProductInterface.iso (codes L) time Q.code Q.map F.collapse).hom ≫
        JTJointRelativeGraphFamily.originalParameter F)

private theorem parameterAlong_app {A I : Type} [SmallCategory A] [SmallCategory I]
    {W : Source} {x y : Vertex W}
    {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
    (F : Family Q L time) (O : I ⥤ A) (N : I ⥤ NecklaceCode)
    (n : N ⟶ O ⋙ codes L) (p : I) :
    (parameterAlong F O N n).app p =
      ((n.app p).map ⊗ₘ 𝟙 (J.obj (time.obj (O.obj p)))) ≫ F.parameter (O.obj p) := by
  rw [parameterAlong, NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    JTSharedInsertionPhaseGraph.reindexedProductMap_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.id_comp]
  rfl

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The complete shared insertion choices and coefficient chain, before triangle fillers. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- Keep the original source object and every original native operator. -/
abbrev original := JTSharedInsertionCoarseNative.original F j

/-- The actual complete corrected coarse label. -/
abbrev labels := JTSharedInsertionCoarseLabels.labels F j

/-- The ENTIRE original time, independently of the tuple/filler clocks. -/
abbrev oldTime := original F j ⋙ time

/-- The original coefficient degree at the unchanged original source. -/
abbrev oldDegrees := original F j ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

/-- The actual shared-chain projection; every coefficient lift is retained. -/
abbrev coefficientProjection := JTSharedInsertionChoices.toOriginal F j

/-- Whole coarse native code multiplied by the complete original time. -/
abbrev X := JTGraphCoveredProductInterface.product (codes (labels F j)) (oldTime F j)

/-- Restrict the EXISTING original Family parameter along the exact coarse assembly. -/
def coarseParameter : X F j ⟶ oldDegrees F j ⋙ J :=
  parameterAlong F (original F j) (codes (labels F j))
    (JTSharedInsertionCoarseNative.assembly F j)

/-- Its entire component is exactly the original parameter after the full native assembly. -/
theorem coarseParameter_app (p : Index F j) :
    (coarseParameter F j).app p =
      (((JTSharedInsertionCoarseNative.assembly F j).app p).map ⊗ₘ
        𝟙 (J.obj ((oldTime F j).obj p))) ≫ F.parameter ((original F j).obj p) :=
  parameterAlong_app F (original F j) (codes (labels F j))
    (JTSharedInsertionCoarseNative.assembly F j) p

/-- ALL assignments lifting that whole original-time parameter are kept. -/
abbrev graph := JTPrismChainGraphCover.cover
  (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The complete native/time coordinate of every lifted graph point. -/
abbrev projection : graph F j ⟶ X F j := JTPrismChainGraphCover.projection
  (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The exact given full shared-chain parameter, not a chosen section. -/
abbrev parameter : graph F j ⟶ JTSharedInsertionChoices.ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter
    (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The full lifted parameter recovers the original entire native/time parameter. -/
theorem parameter_projection :
    parameter F j ≫ Functor.whiskerRight (coefficientProjection F j) J =
      projection F j ≫ coarseParameter F j :=
  JTPrismChainGraphCover.parameter_projection
    (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- Each complete original-time graph is a trivial-fibration cover of its whole product. -/
theorem projection_trivialFibration (p : Index F j) :
    trivialFibrations SSet.{0} ((projection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration
    (X F j) (coarseParameter F j) (coefficientProjection F j)
    (JTSharedInsertionChoices.toOriginal_surjective F j) p

end
end DaggerModels.PartII.JTSharedInsertionCoarseGraph
