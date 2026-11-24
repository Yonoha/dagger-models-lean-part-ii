import DaggerModelsPartII.JTNativeRestrictionIndex
import DaggerModelsPartII.JTNativePulledFamilyDiagram

/-!
Native restriction is natural across the entire original decorated-label
diagram. A morphism retains the actual commuting native square and the original
coefficient-degree operator. The label equation is just presheaf composition;
no normalized-cut or corrected-label coherence is claimed here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeRestrictionLabels

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (codes)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev I (W : Source) (x y : Vertex W) :=
  DecoratedNecklaceHomDiagram.Index W x y
private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev presheaf (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable (L : A ⥤ I W x y)

private instance : (pr W x y).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

/-- All native restrictions of the original varying code. -/
abbrev Index := JTNativeRestrictionIndex.Index (codes L)

/-- Retain the original coefficient-degree diagram. -/
abbrev degree := L ⋙ pr W x y ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory

/-- The actual pulled ordered label, with its original coefficient degree. -/
abbrev label (a : Index L) : I W x y :=
  JTNativePulledCutComparison.label (L.obj a.right) a.hom

private abbrev restrictionOperator (a : Index L) :
    (a.left, (degree L).obj a.right) ⟶
      ((codes L).obj a.right, (degree L).obj a.right) :=
  (a.hom, 𝟙 ((degree L).obj a.right))

private abbrev mixedOperator {a b : Index L} (f : a ⟶ b) :
    (a.left, (degree L).obj a.right) ⟶ (b.left, (degree L).obj b.right) :=
  (f.left, (degree L).map f.right)

/-- A commuting native square and old decorated arrow give the exact mixed arrow. -/
def labelMap {a b : Index L} (f : a ⟶ b) : label L a ⟶ label L b := by
  let k := (degree L).map f.right
  refine (CategoryOfElements.homMk (label L b).unop (label L a).unop
    (mixedOperator L f).op ?_).op
  change (presheaf W x y).map (mixedOperator L f).op
      ((presheaf W x y).map (restrictionOperator L b).op
        (L.obj b.right).unop.2) =
    (presheaf W x y).map (restrictionOperator L a).op
      (L.obj a.right).unop.2
  have ha : (presheaf W x y).map ((pr W x y).map (L.map f.right)).op
      (L.obj b.right).unop.2 = (L.obj a.right).unop.2 :=
    (L.map f.right).unop.property
  rw [← ha, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  have h : (restrictionOperator L b).op ≫ (mixedOperator L f).op =
      ((pr W x y).map (L.map f.right)).op ≫
        (restrictionOperator L a).op := by
    rw [← op_comp, ← op_comp]
    apply congrArg Quiver.Hom.op
    apply Prod.ext
    · exact f.w
    · exact (Category.comp_id k).trans (Category.id_comp k).symm
  exact congrArg (fun u ↦ (presheaf W x y).map u (L.obj b.right).unop.2) h

/-- Pull back all original labels, retaining every original and native operator. -/
def labels : Index L ⥤ I W x y where
  obj := label L
  map := labelMap L
  map_id a := by
    apply (pr W x y).map_injective
    change (𝟙 a.left, (degree L).map (𝟙 a.right)) =
      (𝟙 a.left, 𝟙 ((degree L).obj a.right))
    exact Prod.ext rfl ((degree L).map_id a.right)
  map_comp f g := by
    apply (pr W x y).map_injective
    change (f.left ≫ g.left, (degree L).map (f.right ≫ g.right)) =
      (f.left ≫ g.left, (degree L).map f.right ≫ (degree L).map g.right)
    exact Prod.ext rfl ((degree L).map_comp f.right g.right)

/-- Both operators are the original commuting-square components. -/
theorem labels_projection {a b : Index L} (f : a ⟶ b) :
    (pr W x y).map ((labels L).map f) = (f.left, (degree L).map f.right) := rfl

/-- The native restriction itself compares naturally to the original label. -/
def toOriginal : labels L ⟶ JTNativeRestrictionIndex.projection (codes L) ⋙ L where
  app a := JTNativePulledCutComparison.toOriginal (L.obj a.right) a.hom
  naturality {a b} f := by
    apply (pr W x y).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    change (f.left ≫ b.hom, (degree L).map f.right ≫ 𝟙 _) =
      (a.hom ≫ (codes L).map f.right, 𝟙 _ ≫ (degree L).map f.right)
    exact Prod.ext f.w
      ((Category.comp_id _).trans (Category.id_comp _).symm)

end
end DaggerModels.PartII.JTNativeRestrictionLabels
