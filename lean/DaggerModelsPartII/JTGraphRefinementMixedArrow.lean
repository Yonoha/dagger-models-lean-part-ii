import DaggerModelsPartII.JTGraphRefinement
import DaggerModelsPartII.JTTargetCommaPullbackComparison

/-!
# Mixed operators of exact graph refinements over the original fixed target

The decorated operator governs both the native code and the coefficient.
A map preserves the full graph parameter and the specified map to the fixed target.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace CartesianMonoidalCategory

namespace DaggerModels.PartII.JTGraphRefinementMixedArrow

open JTGraphRefinement JTNecklaceEndpointCylinder
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

abbrev Base := DecoratedNecklaceHomDiagram.Index W x y
abbrev projection := OrderedLabelElements.projection W (boundaryPoint W x y)

abbrev base (D : Refinement W x y Q) : Base (W := W) (x := x) (y := y) :=
  OrderedLabelElements.mk W (boundaryPoint W x y) D.code D.degree D.label

variable {D E G : Refinement W x y Q}

/-- A mixed arrow over the same actual raw target. -/
@[ext]
structure Arrow (D E : Refinement W x y Q) where
  label : base D ⟶ base E
  parameter : D.parameter ≫ J.map ((projection.map label).2) =
    ((projection.map label).1).map ≫ E.parameter
  collapse : (projection.map label).1 ≫ E.collapse = D.collapse

/-- The native operator acts on the whole internal necklace. -/
abbrev Arrow.native (a : Arrow D E) : D.code ⟶ E.code := (projection.map a.label).1

/-- The coefficient operator is the original simplex map. -/
abbrev Arrow.coefficient (a : Arrow D E) : D.degree ⟶ E.degree := (projection.map a.label).2

private def identity (D : Refinement W x y Q) : Arrow D D where
  label := 𝟙 (base D)
  parameter := by
    rw [projection.map_id]
    change D.parameter ≫ J.map (𝟙 D.degree) = 𝟙 D.code.toSSet ≫ D.parameter
    rw [J.map_id, Category.comp_id, Category.id_comp]
  collapse := by
    rw [projection.map_id]
    exact Category.id_comp _

private def compose (a : Arrow D E) (b : Arrow E G) : Arrow D G where
  label := a.label ≫ b.label
  parameter := by
    rw [projection.map_comp]
    change D.parameter ≫ J.map (a.coefficient ≫ b.coefficient) =
      (a.native.map ≫ b.native.map) ≫ G.parameter
    rw [J.map_comp, ← Category.assoc, a.parameter, Category.assoc, b.parameter, Category.assoc]
  collapse := by
    rw [projection.map_comp]
    change (a.native ≫ b.native) ≫ G.collapse = D.collapse
    rw [Category.assoc, b.collapse, a.collapse]

instance : SmallCategory (Refinement W x y Q) where
  Hom := Arrow
  id := identity
  comp := compose
  id_comp _ := Arrow.ext (Category.id_comp _)
  comp_id _ := Arrow.ext (Category.comp_id _)
  assoc _ _ _ := Arrow.ext (Category.assoc _ _ _)

def labels (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    Refinement W x y Q ⥤ Base (W := W) (x := x) (y := y) where
  obj := base
  map a := a.label
  map_id _ := rfl
  map_comp _ _ := rfl

theorem traversal_map {T U : NecklaceCode} {k l : SimplexCategory}
    (u : T ⟶ U) (b : k ⟶ l) (s : T.toSSet ⟶ J.obj k) :
    (lift (𝟙 T.toSSet) s ≫ (cylinder T).app k) ≫
        (nativeMap u k ≫ (value U).map b) =
      lift u.map (s ≫ J.map b) ≫ (cylinder U).app l := by
  have hf : (JTXiEndpointCollapse.parameterProduct U.toSSet).map b =
      𝟙 U.toSSet ⊗ₘ J.map b := rfl
  have h : lift (𝟙 T.toSSet) s ≫ (u.map ⊗ₘ J.map b) =
      lift u.map (s ≫ J.map b) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc,
        Category.id_comp]
    · simp only [Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
  rw [Category.assoc, ← Category.assoc ((cylinder T).app k),
    nativeMap_cylinder, Category.assoc, ← (cylinder U).naturality b, hf,
    ← Category.assoc ((u.map ⊗ₘ 𝟙 (J.obj k))),
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, ← Category.assoc, h]

private theorem traversal_comm (a : D ⟶ E) :
    (lift (𝟙 D.code.toSSet) D.parameter ≫
      (cylinder D.code).app D.degree) ≫
        (nativeMap a.native D.degree ≫ (value E.code).map a.coefficient) =
      a.native.map ≫ lift (𝟙 E.code.toSSet) E.parameter ≫ (cylinder E.code).app E.degree := by
  rw [traversal_map, a.parameter, ← Category.assoc, CartesianMonoidalCategory.comp_lift,
    Category.comp_id]

/-- Evaluate a mixed operator on the literal cylinders and exact internal graphs. -/
def presentationArrow (a : D ⟶ E) : D.toComma.left ⟶ E.toComma.left := by
  refine ⟨a.label, CostructuredArrow.homMk a.native ?_⟩
  apply Under.UnderMorphism.ext
  change a.native.map ≫ lift (𝟙 E.code.toSSet) E.parameter ≫ (cylinder E.code).app E.degree =
    (lift (𝟙 D.code.toSSet) D.parameter ≫
      (cylinder D.code).app D.degree) ≫
      (nativeMap a.native D.degree ≫ (value E.code).map a.coefficient)
  exact (traversal_comm a).symm

/-- Evaluation is an arrow over the same original raw target. -/
def commaArrow (a : D ⟶ E) : D.toComma ⟶ E.toComma :=
  CostructuredArrow.homMk (presentationArrow a) (by
    apply NecklacesOver.Hom.ext
    change ((DecoratedCylinderNecklacePresentation.toTarget W x y).map
      (presentationArrow a)).hom ≫ E.collapse = D.collapse
    rw [DecoratedCylinderNecklacePresentation.toTarget_map_hom]
    exact a.collapse)

/-- All mixed arrows evaluate functorially in the original fixed-target comma. -/
def evaluate (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    Refinement W x y Q ⥤
      CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q where
  obj := Refinement.toComma
  map := commaArrow
  map_id D := by
    apply CostructuredArrow.hom_ext
    apply JTTargetCommaPullback.operator_ext
    · rfl
    · let P := BoundaryNecklaceComma.sourceCode
        (DecoratedCylinderNecklacePresentation.underDiagram W x y)
      change (projection.map (𝟙 (base D))).1 = P.map (𝟙 D.toComma.left)
      rw [projection.map_id, P.map_id]
      rfl
  map_comp a b := by
    apply CostructuredArrow.hom_ext
    apply JTTargetCommaPullback.operator_ext
    · rfl
    · let P := BoundaryNecklaceComma.sourceCode
        (DecoratedCylinderNecklacePresentation.underDiagram W x y)
      change (projection.map (a.label ≫ b.label)).1 =
        P.map (presentationArrow a ≫ presentationArrow b)
      rw [projection.map_comp, P.map_comp]
      rfl

theorem evaluate_native (a : D ⟶ E) :
    ((evaluate Q).map a).left.fiber.left = a.native := rfl

instance (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) : (evaluate Q).Faithful where
  map_injective h := Arrow.ext (congrArg (fun a ↦ a.left.base) h)

end

end DaggerModels.PartII.JTGraphRefinementMixedArrow
