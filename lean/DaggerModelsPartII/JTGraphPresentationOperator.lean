import DaggerModelsPartII.JTGraphToPresentationArrow

/-!
# Morphisms between graph presentations

The native necklace map and simplex operator are both retained in the
decorated label base, while the parameter equation supplies the fiber arrow.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphPresentationOperator

open JTProjectiveOrderedFiberComparison OrderedNecklaceLabelDiagram
open OrderedNecklaceVertexPoints JTRealizedLabelEndpoints
open JTGraphRefinement

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {S T : NecklaceCode} {k l : SimplexCategory}

/-- The ordered-label arrow with underlying operator `(g, j)`. -/
private def baseArrow (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z) :
    OrderedLabelElements.mk W (boundaryPoint W x y) S k z ⟶
      OrderedLabelElements.mk W (boundaryPoint W x y) T l z' := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let a : (S, k) ⟶ (T, l) := (g, j)
  refine (CategoryOfElements.homMk
    (P.elementsMk (op (T, l)) z') (P.elementsMk (op (S, k)) z)
    a.op ?_).op
  exact hlabel

private theorem traversal_natural (g : S ⟶ T) (j : k ⟶ l)
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hparam : s ≫ J.map j = g.map ≫ s') :
    g.map ≫ (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s' ≫
      (JTNecklaceEndpointCylinder.cylinder T).app l) =
    (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
      (JTNecklaceEndpointCylinder.cylinder S).app k) ≫
      (JTNecklaceEndpointCylinder.nativeMap g k ≫
        (JTNecklaceEndpointCylinder.value T).map j) := by
  have hnative : g.map ≫ CartesianMonoidalCategory.lift (𝟙 T.toSSet) s' =
      CartesianMonoidalCategory.lift (𝟙 S.toSSet) (s ≫ J.map j) ≫
        (g.map ⊗ₘ 𝟙 (J.obj l)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.lift_fst_assoc,
        CartesianMonoidalCategory.tensorHom_fst, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
      exact hparam.symm
  have hdegree : CartesianMonoidalCategory.lift (𝟙 S.toSSet) (s ≫ J.map j) =
      CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
        (𝟙 S.toSSet ⊗ₘ J.map j) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.lift_snd_assoc,
        CartesianMonoidalCategory.tensorHom_snd]
  have htraversal :
      CartesianMonoidalCategory.lift (𝟙 S.toSSet) (s ≫ J.map j) ≫
        (JTNecklaceEndpointCylinder.cylinder S).app l =
      (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
        (JTNecklaceEndpointCylinder.cylinder S).app k) ≫
        (JTNecklaceEndpointCylinder.value S).map j := by
    rw [hdegree, Category.assoc]
    change CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
      ((JTXiEndpointCollapse.parameterProduct S.toSSet).map j ≫
        (JTNecklaceEndpointCylinder.cylinder S).app l) = _
    have hn := (JTNecklaceEndpointCylinder.cylinder S).naturality j
    change (JTXiEndpointCollapse.parameterProduct S.toSSet).map j ≫
        (JTNecklaceEndpointCylinder.cylinder S).app l =
      (JTNecklaceEndpointCylinder.cylinder S).app k ≫
        (JTNecklaceEndpointCylinder.value S).map j at hn
    simpa only [Category.assoc] using congrArg
      (fun f ↦ CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫ f) hn
  calc
    _ = (CartesianMonoidalCategory.lift (𝟙 S.toSSet) (s ≫ J.map j) ≫
          (g.map ⊗ₘ 𝟙 (J.obj l))) ≫
          (JTNecklaceEndpointCylinder.cylinder T).app l := by
            rw [← Category.assoc, hnative]
    _ = CartesianMonoidalCategory.lift (𝟙 S.toSSet) (s ≫ J.map j) ≫
          (JTNecklaceEndpointCylinder.cylinder S).app l ≫
          JTNecklaceEndpointCylinder.nativeMap g l := by
            simp only [Category.assoc, JTNecklaceEndpointCylinder.nativeMap_cylinder]
    _ = (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
          (JTNecklaceEndpointCylinder.cylinder S).app k) ≫
          (JTNecklaceEndpointCylinder.value S).map j ≫
          JTNecklaceEndpointCylinder.nativeMap g l := by
            simpa only [Category.assoc] using congrArg
              (fun f ↦ f ≫ JTNecklaceEndpointCylinder.nativeMap g l) htraversal
    _ = _ := by
      simp only [Category.assoc, JTNecklaceEndpointCylinder.nativeMap_parameter_natural]

/-- The fiber component has native necklace map `g`. -/
private def fiberArrow (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z)
    (hTraversal :
      g.map ≫ (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s' ≫
        (JTNecklaceEndpointCylinder.cylinder T).app l) =
      (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
        (JTNecklaceEndpointCylinder.cylinder S).app k) ≫
        (JTNecklaceEndpointCylinder.nativeMap g k ≫
          (JTNecklaceEndpointCylinder.value T).map j)) :
    ((BoundaryNecklaceComma.fiberDiagram
      (DecoratedCylinderNecklacePresentation.underDiagram W x y)).map
      (baseArrow g j z z' hlabel)).toFunctor.obj
      (presentation W x y S k z s).fiber ⟶
    (presentation W x y T l z' s').fiber := by
  refine CostructuredArrow.homMk g ?_
  apply Under.UnderMorphism.ext
  exact hTraversal

/-- A graph presentation morphism determined by the actual reduced-cylinder traversal equation. -/
def presentationArrowOfTraversal (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z)
    (hTraversal :
      g.map ≫ (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s' ≫
        (JTNecklaceEndpointCylinder.cylinder T).app l) =
      (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
        (JTNecklaceEndpointCylinder.cylinder S).app k) ≫
        (JTNecklaceEndpointCylinder.nativeMap g k ≫
          (JTNecklaceEndpointCylinder.value T).map j)) :
    presentation W x y S k z s ⟶ presentation W x y T l z' s' where
  base := baseArrow g j z z' hlabel
  fiber := fiberArrow g j z z' s s' hlabel hTraversal

theorem presentationArrowOfTraversal_base_projection (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z)
    (hTraversal :
      g.map ≫ (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s' ≫
        (JTNecklaceEndpointCylinder.cylinder T).app l) =
      (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
        (JTNecklaceEndpointCylinder.cylinder S).app k) ≫
        (JTNecklaceEndpointCylinder.nativeMap g k ≫
          (JTNecklaceEndpointCylinder.value T).map j)) :
    (OrderedLabelElements.projection W (boundaryPoint W x y)).map
      (presentationArrowOfTraversal g j z z' s s' hlabel hTraversal).base = (g, j) := rfl

theorem presentationArrowOfTraversal_fiber_left (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z)
    (hTraversal :
      g.map ≫ (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s' ≫
        (JTNecklaceEndpointCylinder.cylinder T).app l) =
      (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
        (JTNecklaceEndpointCylinder.cylinder S).app k) ≫
        (JTNecklaceEndpointCylinder.nativeMap g k ≫
          (JTNecklaceEndpointCylinder.value T).map j)) :
    (presentationArrowOfTraversal g j z z' s s' hlabel hTraversal).fiber.left = g := rfl

/-- A graph presentation morphism with native and parameter operators. -/
def presentationArrow (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z)
    (hparam : s ≫ J.map j = g.map ≫ s') :
    presentation W x y S k z s ⟶ presentation W x y T l z' s' :=
  presentationArrowOfTraversal g j z z' s s' hlabel (traversal_natural g j s s' hparam)

theorem presentationArrow_base_projection (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z)
    (hparam : s ≫ J.map j = g.map ≫ s') :
    (OrderedLabelElements.projection W (boundaryPoint W x y)).map
      (presentationArrow g j z z' s s' hlabel hparam).base = (g, j) := rfl

theorem presentationArrow_fiber_left (g : S ⟶ T) (j : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op k))
    (z' : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l))
    (s : S.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
    (hlabel : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map
      j.op (((orderedNecklaceLabels W (boundaryPoint W x y)).map g.op).app (op l) z') = z)
    (hparam : s ≫ J.map j = g.map ≫ s') :
    (presentationArrow g j z z' s s' hlabel hparam).fiber.left = g := rfl

end

end DaggerModels.PartII.JTGraphPresentationOperator
