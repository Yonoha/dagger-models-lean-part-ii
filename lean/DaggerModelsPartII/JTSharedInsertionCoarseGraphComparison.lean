import DaggerModelsPartII.JTSharedInsertionCoarseGraph
import DaggerModelsPartII.JTSharedInsertionOldGraph
import DaggerModelsPartII.JTSharedInsertionCoarseComparisonNative
import DaggerModelsPartII.JTPrismChainGraphTransport

/-!
# Compare every original-time coefficient lift of the actual old and coarse labels

The checked strict native assembly triangle gives the complete original
parameter square before Q. Existing graph transport retains all assignments
and the entire original time, with identity common coefficient operator.
No parameter section, raw equation or weak-source conclusion is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSharedInsertionCoarseGraphComparison

noncomputable section

private abbrev J := GroupoidSimplex.parameter

private theorem product_app {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (n : N ⟶ M) (t : C ⥤ SimplexCategory) (p : C) :
    (JTSharedInsertionPhaseGraph.mapWithTime n t).app p =
      (n.app p).map ⊗ₘ 𝟙 (J.obj (t.obj p)) := rfl

private theorem tensor_parameter {S M T I P : SSet.{0}}
    (f : S ⟶ M) (g : M ⟶ T) (u : S ⟶ T) (h : f ≫ g = u)
    (p : T ⊗ I ⟶ P) :
    (f ⊗ₘ 𝟙 I) ≫ ((g ⊗ₘ 𝟙 I) ≫ p) = (u ⊗ₘ 𝟙 I) ≫ p := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, h]

private theorem whisker_identity {C : Type} [SmallCategory C] (K : C ⥤ SimplexCategory) :
    Functor.whiskerRight (𝟙 K) J = 𝟙 (K ⋙ J) := by
  apply NatTrans.ext
  funext p
  exact J.map_id (K.obj p)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The unchanged shared insertion index, before triangle choices. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- Act by the existing actual native comparison and identically on ENTIRE original time. -/
def productMap : JTSharedInsertionOldGraph.X F j ⟶ JTSharedInsertionCoarseGraph.X F j :=
  JTSharedInsertionPhaseGraph.mapWithTime
    (JTSharedInsertionCoarseComparisonNative.comparison F j)
    (JTSharedInsertionCoarseGraph.oldTime F j)

set_option maxHeartbeats 400000 in
/-- Its whole component retains the full original-time coordinate. -/
theorem productMap_app (p : Index F j) :
    ((productMap F j).app p : (JTSharedInsertionOldGraph.X F j).obj p ⟶
      (JTSharedInsertionCoarseGraph.X F j).obj p) =
      ((((JTSharedInsertionCoarseComparisonNative.comparison F j).app p).map ⊗ₘ
        𝟙 (J.obj ((JTSharedInsertionCoarseGraph.oldTime F j).obj p))) :
          (JTSharedInsertionOldGraph.X F j).obj p ⟶
            (JTSharedInsertionCoarseGraph.X F j).obj p) :=
  product_app (JTSharedInsertionCoarseComparisonNative.comparison F j)
    (JTSharedInsertionCoarseGraph.oldTime F j) p

set_option maxHeartbeats 400000 in
/-- The actual original Family parameter commutes with the WHOLE product map. -/
theorem parameter_square :
    productMap F j ≫ JTSharedInsertionCoarseGraph.coarseParameter F j =
      JTSharedInsertionOldGraph.coarseParameter F j := by
  apply NatTrans.ext
  funext p
  rw [NatTrans.comp_app, productMap_app, JTSharedInsertionCoarseGraph.coarseParameter_app,
    JTSharedInsertionOldGraph.coarseParameter_app]
  apply tensor_parameter
  exact congrArg NecklaceCode.Hom.map
    (NatTrans.congr_app (JTSharedInsertionCoarseComparisonNative.comparison_assembly F j) p)

/-- Every old coefficient assignment maps canonically to its corresponding coarse assignment. -/
def map : JTSharedInsertionOldGraph.graph F j ⟶ JTSharedInsertionCoarseGraph.graph F j :=
  JTPrismChainGraphTransport.map
    (JTSharedInsertionOldGraph.X F j) (JTSharedInsertionCoarseGraph.X F j)
    (JTSharedInsertionOldGraph.coarseParameter F j)
    (JTSharedInsertionCoarseGraph.coarseParameter F j)
    (JTSharedInsertionChoices.toOriginal F j) (JTSharedInsertionChoices.toOriginal F j)
    (𝟙 (JTSharedInsertionChoices.ordinals F j))
    (Category.id_comp _) (productMap F j) (parameter_square F j)

/-- The complete native/time projection square is exact on ALL assignments. -/
theorem map_projection :
    map F j ≫ JTSharedInsertionCoarseGraph.projection F j =
      JTSharedInsertionOldGraph.projection F j ≫ productMap F j :=
  JTPrismChainGraphTransport.map_projection
    (JTSharedInsertionOldGraph.X F j) (JTSharedInsertionCoarseGraph.X F j)
    (JTSharedInsertionOldGraph.coarseParameter F j)
    (JTSharedInsertionCoarseGraph.coarseParameter F j)
    (JTSharedInsertionChoices.toOriginal F j) (JTSharedInsertionChoices.toOriginal F j)
    (𝟙 (JTSharedInsertionChoices.ordinals F j))
    (Category.id_comp _) (productMap F j) (parameter_square F j)

/-- The complete shared coefficient parameter is unchanged by graph comparison. -/
theorem map_parameter :
    map F j ≫ JTSharedInsertionCoarseGraph.parameter F j =
      JTSharedInsertionOldGraph.parameter F j := by
  have h := JTPrismChainGraphTransport.map_parameter
    (JTSharedInsertionOldGraph.X F j) (JTSharedInsertionCoarseGraph.X F j)
    (JTSharedInsertionOldGraph.coarseParameter F j)
    (JTSharedInsertionCoarseGraph.coarseParameter F j)
    (JTSharedInsertionChoices.toOriginal F j) (JTSharedInsertionChoices.toOriginal F j)
    (𝟙 (JTSharedInsertionChoices.ordinals F j))
    (Category.id_comp _) (productMap F j) (parameter_square F j)
  simpa only [whisker_identity, Category.comp_id] using h

end
end DaggerModels.PartII.JTSharedInsertionCoarseGraphComparison
