import DaggerModelsPartII.JTIdentityRowRealization
import DaggerModelsPartII.DecoratedCylinderNecklacePresentation

/-!
# Graph presentations over the original reduced cylinder

A whole parameter map on a native necklace determines a cylinder traversal.
A strict refinement retains the label, parameter map, and comparison over the
original raw target, so the same data can be used when adjoining another bead.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphRefinement

open OrdinaryJTRealization JTReversalInput ReversalDiscreteFreeColimits
open JTProjectiveOrderedFiberComparison JTNecklaceLabelRealization
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints JTRealizedLabelEndpoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev F := discreteFree.{0}
private abbrev E := (single 1).toSSet
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The original identity bead coefficient extended constantly in the entire
parameter simplex. -/
def identityCoefficient (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) (k : SimplexCategory) :
    (diagramMappingSpace (F.obj E) W).obj (op k) :=
  (diagramTensor (F.obj E)).map
    (SSet.stdSimplex.map (SimplexCategory.const k ⦋0⦌ 0)) ≫
      JTIdentityRowRealization.identityEdgeLabel W x

/-- All parameter paths through the identity bead realize to the same raw
joint. The equality is on the whole product, before choosing a path. -/
theorem realizedIdentityCoefficient (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) (k : SimplexCategory) :
    realizedLabel E W k (identityCoefficient W x k) =
      SSet.stdSimplex.isTerminalObj₀.from (E ⊗ J.obj k) ≫
        SSet.yonedaEquiv.symm (rawVertex W x) := by
  unfold identityCoefficient
  rw [← realizedLabel_natural_k, JTIdentityRowRealization.realizedIdentityEdgeLabel]
  rw [← Category.assoc]
  congr 1

/-- Realize the graph of a whole parameter map against the given coefficient. -/
def realizeGraph {X : SSet.{0}} (W : Source) (k : SimplexCategory)
    (s : X ⟶ J.obj k) (η : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    X ⟶ R W :=
  CartesianMonoidalCategory.lift (𝟙 X) s ≫ realizedLabel X W k η

/-- Restricting the entire realized graph amounts to restricting its
parameter map and coefficient along the same horizontal map. -/
theorem realizeGraph_comp {X Y : SSet.{0}} (W : Source) (k : SimplexCategory)
    (f : X ⟶ Y) (s : Y ⟶ J.obj k)
    (η : (diagramMappingSpace (F.obj Y) W).obj (op k)) :
    f ≫ realizeGraph W k s η = realizeGraph W k (f ≫ s)
      (Functor.whiskerRight (F.map f) (tensorRight (SSet.stdSimplex.obj k)) ≫ η) := by
  have h : f ≫ CartesianMonoidalCategory.lift (𝟙 Y) s =
      CartesianMonoidalCategory.lift (𝟙 X) (f ≫ s) ≫ (f ⊗ₘ 𝟙 (J.obj k)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst_assoc,
        Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.lift_snd, Category.comp_id]
  unfold realizeGraph
  rw [← Category.assoc, h, Category.assoc, realizedLabel_natural_X]

/-- Inserting a parameter into a larger split ordinal and extending the
coefficient along the retraction preserves the complete realized graph. -/
theorem realizeGraph_split {X : SSet.{0}} (W : Source) {k l : SimplexCategory}
    (j : k ⟶ l) (r : l ⟶ k) (h : j ≫ r = 𝟙 k)
    (s : X ⟶ J.obj k) (η : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    realizeGraph W l (s ≫ J.map j)
      ((diagramTensor (F.obj X)).map (SSet.stdSimplex.map r) ≫ η) =
      realizeGraph W k s η := by
  have hg : CartesianMonoidalCategory.lift (𝟙 X) (s ≫ J.map j) =
      CartesianMonoidalCategory.lift (𝟙 X) s ≫ (𝟙 X ⊗ₘ J.map j) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst, Category.comp_id]
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.lift_snd_assoc]
  unfold realizeGraph
  rw [hg, Category.assoc, realizedLabel_natural_k, ← Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, h]
  have hr : (diagramTensor (F.obj X)).map (SSet.stdSimplex.{0}.map (𝟙 k)) ≫ η = η := by
    rw [SSet.stdSimplex.{0}.map_id, (diagramTensor (F.obj X)).map_id, Category.id_comp]
  erw [hr]

/-- Every graph of a parameter map on the original native code is under the
whole fixed boundary in the original reduced cylinder. -/
theorem traversal_boundary (T : NecklaceCode) (k : SimplexCategory)
    (s : T.toSSet ⟶ J.obj k) :
    JTNecklaceEndpointCylinder.endpointInclusion T ≫
      (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s ≫
        (JTNecklaceEndpointCylinder.cylinder T).app k) =
      (JTNecklaceEndpointCylinder.boundary T).app k := by
  let b := JTNecklaceEndpointCylinder.endpointInclusion T
  let g := CartesianMonoidalCategory.lift (𝟙 JTXiEndpointCollapse.boundary) (b ≫ s)
  have h : b ≫ CartesianMonoidalCategory.lift (𝟙 T.toSSet) s =
      g ≫ (b ⊗ₘ 𝟙 (J.obj k)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [g, Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst_assoc,
        Category.comp_id, Category.id_comp]
    · simp only [g, Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.lift_snd, Category.comp_id]
  change b ≫ _ = _
  rw [← Category.assoc, h, Category.assoc, (JTNecklaceEndpointCylinder.isPushout T k).w]
  simp only [g, ← Category.assoc, CartesianMonoidalCategory.lift_fst, Category.id_comp]

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- An actual decorated-cylinder presentation, with the same native source
and label code and with horizontal coordinate the identity. -/
def presentation (T : NecklaceCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k))
    (s : T.toSSet ⟶ J.obj k) : DecoratedCylinderNecklacePresentation.Presentation W x y where
  base := OrderedLabelElements.mk W (boundaryPoint W x y) T k z
  fiber := CostructuredArrow.mk (Y := T) (Under.homMk
    (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s ≫
      (JTNecklaceEndpointCylinder.cylinder T).app k) (traversal_boundary T k s))

/-- The actual target functor evaluates the whole graph. -/
theorem presentation_target_map (T : NecklaceCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k))
    (s : T.toSSet ⟶ J.obj k) :
    ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
      (presentation W x y T k z s)).map = realizeGraph W k s (orderedLabel W x y T k z) := by
  change (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s ≫
      (JTNecklaceEndpointCylinder.cylinder T).app k) ≫
      JTNecklaceEndpointCylinder.descend W x y T k z = _
  rw [Category.assoc, JTNecklaceEndpointCylinder.descend_cylinder]
  rfl

/-- A strict over-target comparison that retains the data of its graph. -/
structure Refinement (Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)) where
  code : NecklaceCode
  degree : SimplexCategory
  label : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op code)).obj (op degree)
  parameter : code.toSSet ⟶ J.obj degree
  collapse : code ⟶ Q.code
  comm : realizeGraph W degree parameter (orderedLabel W x y code degree label) =
    collapse.map ≫ Q.map

variable {W x y}

/-- Forgetting the graph data gives an object of the original target comma. -/
def Refinement.toComma {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}
    (D : Refinement W x y Q) :
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q :=
  CostructuredArrow.mk (Y := presentation W x y D.code D.degree D.label D.parameter)
    { hom := D.collapse
      w := by rw [presentation_target_map, D.comm] }

end

end DaggerModels.PartII.JTGraphRefinement
