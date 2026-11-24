import DaggerModelsPartII.JTCommonCoefficientCylinder
import DaggerModelsPartII.JTCommonCoefficientFinalOperator

/-!
# Comparison with the existing cylinder over the final coefficient
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter

theorem graphPrism_toFinal {X : SSet.{0}} {k b : SimplexCategory}
    (c : k ⟶ b) (s : X ⟶ J.obj k) (n : SimplexCategory) :
    graphPrism c s n ≫ (X ◁ J.map (toFinal c n)) =
      JTHigherGraphPrismCylinder.graphPrism (s ≫ J.map c) n := by
  simp only [← MonoidalCategory.id_tensorHom]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, JTHigherGraphPrismCylinder.graphPrism, Category.assoc,
      tensorHom_fst, lift_fst, Category.comp_id]
  · calc
      _ = (s ⊗ₘ 𝟙 (J.obj n)) ≫ paired c n ≫ J.map (toFinal c n) := by
        rw [Category.assoc, tensorHom_snd, ← Category.assoc, graphPrism, lift_snd,
          Category.assoc]
      _ = ((s ≫ J.map c) ⊗ₘ 𝟙 (J.obj n)) ≫
          JTHigherGroupoidParameterPrism.paired b n := by
        rw [paired_toInterleaved c n (toFinal c n) (toFinal_vertexEquiv c n),
          ← MonoidalCategory.tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom,
          Category.id_comp]
      _ = _ := by rw [JTHigherGraphPrismCylinder.graphPrism, lift_snd]

/-- The entire original cylinder map commutes with passage to the final
coefficient, with the same ordered ends. -/
theorem cylinderMap_toFinal (T : NecklaceCode) {k b : SimplexCategory}
    (c : k ⟶ b) (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    cylinderMap T c s n ≫ (value T).map (toFinal c n) =
      JTHigherGraphPrismCylinder.cylinderMap T (s ≫ J.map c) n := by
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, ← (cylinder T).naturality,
      ← Category.assoc]
    change (graphPrism c s n ≫ (T.toSSet ◁ J.map (toFinal c n))) ≫
      (cylinder T).app (common b n) = _
    rw [graphPrism_toFinal, JTHigherGraphPrismCylinder.cylinderMap_cylinder]
  · rw [← Category.assoc, cylinderMap_boundary, ← (boundary T).naturality,
      JTHigherGraphPrismCylinder.cylinderMap_boundary]
    exact Category.id_comp _

open JTProjectiveOrderedFiberComparison OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram

variable (W : SegalLocalizers.ReverseDaggerSpace.{0})
variable (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NecklaceCode)
variable {k b : SimplexCategory} (c : k ⟶ b) (n : SimplexCategory)
variable (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op (common b n)))

/-- Restrict the original label along the exact map to the final coefficient. -/
def pulledLabel :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op (common k n)) :=
  ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map (toFinal c n).op z

/-- Restricting the final label commutes with both original operators. -/
theorem pulledLabel_map {l m : SimplexCategory} {d : l ⟶ b}
    (f : k ⟶ l) (hf : f ≫ d = c) (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (v : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op (common b m))) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map (map f hf j hj).op
      (pulledLabel W x y T d m v) =
    pulledLabel W x y T c n
      (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map
        (JTHigherInterleavedParameter.mapTime b j).op v) := by
  simp only [pulledLabel, ← FunctorToTypes.map_comp_apply, ← op_comp, map_toFinal]

/-- The entire composite into the original raw realization agrees with
the checked cylinder at the final coefficient. -/
theorem descend_toFinal (s : T.toSSet ⟶ J.obj k) :
    cylinderMap T c s n ≫ descend W x y T (common k n) (pulledLabel W x y T c n z) =
      JTHigherGraphPrismCylinder.cylinderMap T (s ≫ J.map c) n ≫
        descend W x y T (common b n) z := by
  rw [pulledLabel, ← descend_parameter_natural, ← Category.assoc, cylinderMap_toFinal]

end

end DaggerModels.PartII.JTCommonCoefficientParameter
