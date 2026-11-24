import DaggerModelsPartII.JTOrderedLabelJointInsertion

/-! Functorial constant ordered labels and their native point collapse. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTConstantOrderedLabelDiagram

open OrderedNecklaceLabelDiagram
open OrderedNecklaceVertexPoints
open JTConstantOrderedLabel (constantIndex constantIndexHom)

noncomputable section

set_option maxHeartbeats 800000

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev I (W : Source) (z : Vertex W) :=
  OrderedLabelElements.Index W (boundaryPoint W z z)
private abbrev pr (W : Source) (z : Vertex W) :=
  OrderedLabelElements.projection W (boundaryPoint W z z)

variable {A : Type} [SmallCategory A] (W : Source) (z : Vertex W)

private theorem hom_ext {i i' : I W z} {f g : i ⟶ i'}
    (h : (pr W z).map f = (pr W z).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

/-- The exact native and ordinal operators of a constant-label arrow. -/
theorem constantIndexHom_projection {S T : NecklaceCode} {k l : SimplexCategory}
    (f : S ⟶ T) (r : k ⟶ l) :
    (pr W z).map (constantIndexHom W z f r) = (f, r) := by
  rfl

/-- Constant labels of changing necklaces and degrees form a decorated diagram. -/
def diagram (T : A ⥤ NecklaceCode) (K : A ⥤ SimplexCategory) : A ⥤ I W z where
  obj a := constantIndex W z (T.obj a) (K.obj a)
  map f := constantIndexHom W z (T.map f) (K.map f)
  map_id a := by
    apply hom_ext W z
    rw [constantIndexHom_projection, T.map_id, K.map_id, (pr W z).map_id]
    rfl
  map_comp f g := by
    apply hom_ext W z
    rw [(pr W z).map_comp, constantIndexHom_projection,
      constantIndexHom_projection, constantIndexHom_projection,
      T.map_comp, K.map_comp]
    rfl

@[simp] theorem projection_obj (T : A ⥤ NecklaceCode)
    (K : A ⥤ SimplexCategory) (a : A) :
    (pr W z).obj ((diagram W z T K).obj a) = (T.obj a, K.obj a) := rfl

@[simp] theorem projection_map (T : A ⥤ NecklaceCode)
    (K : A ⥤ SimplexCategory) {a b : A} (f : a ⟶ b) :
    (pr W z).map ((diagram W z T K).map f) = (T.map f, K.map f) :=
  constantIndexHom_projection W z (T.map f) (K.map f)

/-- Projection recovers the complete original pair of diagrams. -/
theorem projection_eq (T : A ⥤ NecklaceCode)
    (K : A ⥤ SimplexCategory) :
    diagram W z T K ⋙ pr W z = T.prod' K := by
  refine CategoryTheory.Functor.ext (fun a ↦ projection_obj W z T K a) ?_
  intro a b f
  simpa only [Functor.comp_map, Functor.prod'_map, eqToHom_refl,
    Category.id_comp, Category.comp_id] using projection_map W z T K f

/-- The decorated label with the literal point necklace and zero parameter degree. -/
def pointDiagram : A ⥤ I W z :=
  (Functor.const A).obj (constantIndex W z NecklaceCode.point ⦋0⦌)

@[simp] theorem pointDiagram_obj (a : A) :
    (pointDiagram W z (A := A)).obj a =
      constantIndex W z NecklaceCode.point ⦋0⦌ := rfl

@[simp] theorem pointDiagram_map {a b : A} (f : a ⟶ b) :
    (pointDiagram W z).map f =
      𝟙 (constantIndex W z NecklaceCode.point ⦋0⦌) := rfl

/-- Collapse both native and ordinal coordinates to their actual terminal objects. -/
def toPoint (T : A ⥤ NecklaceCode) (K : A ⥤ SimplexCategory) :
    diagram W z T K ⟶ pointDiagram W z where
  app a := constantIndexHom W z (JTOrderedLabelJointInsertion.toPoint (T.obj a))
    (SimplexCategory.isTerminalZero.from (K.obj a))
  naturality {a b} f := by
    apply hom_ext W z
    simp only [Functor.map_comp, projection_map, pointDiagram_map,
      constantIndexHom_projection]
    apply Prod.ext
    · change T.map f ≫ JTOrderedLabelJointInsertion.toPoint (T.obj b) =
        JTOrderedLabelJointInsertion.toPoint (T.obj a) ≫ 𝟙 NecklaceCode.point
      rw [Category.comp_id]
      exact (JTOrderedLabelJointInsertion.toPointNatural T).naturality f
    · change K.map f ≫ SimplexCategory.isTerminalZero.from (K.obj b) =
        SimplexCategory.isTerminalZero.from (K.obj a) ≫ 𝟙 ⦋0⦌
      rw [Category.comp_id]
      exact SimplexCategory.isTerminalZero.hom_ext _ _

@[simp] theorem toPoint_projection_app (T : A ⥤ NecklaceCode)
    (K : A ⥤ SimplexCategory) (a : A) :
    (pr W z).map ((toPoint W z T K).app a) =
      (JTOrderedLabelJointInsertion.toPoint (T.obj a),
        SimplexCategory.isTerminalZero.from (K.obj a)) :=
  constantIndexHom_projection W z _ _

end

end DaggerModels.PartII.JTConstantOrderedLabelDiagram
