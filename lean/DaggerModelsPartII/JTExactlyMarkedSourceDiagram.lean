import DaggerModelsPartII.JTActualSourceJointSupportTransport
import OriginalCutMapLaws

/-!
# The full original diagram with an exactly transported source cut

The objects retain every source vertex above the specified target joint.
An arrow carries that vertex exactly to the selected target vertex.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTExactlyMarkedSourceDiagram

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTActualSourceJointSupport (usedDegree usedInclusion usedInclusion_mono oldVertexRow
  oldVertexRow_supported_joint)
open JTActualSourceJointSupportTransport (usedOperator usedOperator_inclusion oldVertexRow_map)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open DaggerOriginalProductGadget (orderMap_id_apply)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev cuts (a : A) :=
  {v : Fin (((codes L).obj a).len + 1) // orderMap (F.collapse.app a).map v = j.val}

private def transport {a b : A} (f : a ⟶ b) (v : cuts F j a) : cuts F j b :=
  ⟨orderMap ((codes L).map f).map v.val, by
    have h : (codes L).map f ≫ F.collapse.app b = F.collapse.app a :=
      (F.collapse.naturality f).trans (Category.comp_id _)
    rw [← orderMap_comp_apply]
    exact (congrArg (fun g : (codes L).obj a ⟶ Q.code ↦ orderMap g.map v.val) h).trans v.property⟩

/-- All vertices above the actual target joint, with transport by each original arrow. -/
def vertices : A ⥤ Type where
  obj := cuts F j
  map f := transport F j f
  map_id a := by
    funext v
    apply Subtype.ext
    change orderMap ((codes L).map (𝟙 a)).map v.val = v.val
    rw [(codes L).map_id]
    exact orderMap_id_apply _ _
  map_comp {a b c} f g := by
    funext v
    apply Subtype.ext
    change orderMap ((codes L).map (f ≫ g)).map v.val =
      orderMap ((codes L).map g).map (orderMap ((codes L).map f).map v.val)
    rw [(codes L).map_comp]
    exact orderMap_comp_apply _ _ _

/-- The category retaining the original arrows that exactly carry the chosen cut. -/
abbrev Index := (vertices F j).Elements

/-- Forget the chosen cut, retaining the original object and arrow. -/
abbrev base : Index F j ⥤ A := CategoryOfElements.π (vertices F j)

/-- The exact vertex equation for each arrow in this category. -/
theorem cut_map {a b : Index F j} (f : a ⟶ b) :
    orderMap ((codes L).map f.val).map a.2.val = b.2.val :=
  congrArg Subtype.val f.property

/-- The unchanged old coefficient diagram on the chosen cuts. -/
abbrev degrees := base F j ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

private abbrev supportObj (a : Index F j) := usedDegree F a.1 j a.2.val a.2.property
private abbrev inclusion (a : Index F j) := usedInclusion F a.1 j a.2.val a.2.property

private def supportMap {a b : Index F j} (f : a ⟶ b) :
    supportObj F j a ⟶ supportObj F j b :=
  usedOperator F j f.val a.2.val b.2.val a.2.property b.2.property (cut_map F j f)

private theorem supportMap_fac {a b : Index F j} (f : a ⟶ b) :
    supportMap F j f ≫ inclusion F j b = inclusion F j a ≫ (degrees F j).map f :=
  usedOperator_inclusion F j f.val a.2.val b.2.val a.2.property b.2.property (cut_map F j f)

/-- The entire time support is an ordinal diagram, with no new coefficient choices. -/
def supports : Index F j ⥤ SimplexCategory where
  obj := supportObj F j
  map := supportMap F j
  map_id a := by
    haveI := usedInclusion_mono F a.1 j a.2.val a.2.property
    apply (cancel_mono (inclusion F j a)).mp
    change supportMap F j (𝟙 a) ≫ inclusion F j a = 𝟙 _ ≫ inclusion F j a
    rw [supportMap_fac, (degrees F j).map_id]
    exact (Category.comp_id (inclusion F j a)).trans (Category.id_comp _).symm
  map_comp {a b c} f g := by
    haveI := usedInclusion_mono F c.1 j c.2.val c.2.property
    apply (cancel_mono (inclusion F j c)).mp
    change supportMap F j (f ≫ g) ≫ inclusion F j c =
      (supportMap F j f ≫ supportMap F j g) ≫ inclusion F j c
    rw [supportMap_fac, Category.assoc, supportMap_fac, ← Category.assoc,
      supportMap_fac, Category.assoc, (degrees F j).map_comp]

/-- The used coefficient degrees include naturally in the original ones. -/
def incl : supports F j ⟶ degrees F j where
  app := inclusion F j
  naturality _ _ f := supportMap_fac F j f

/-- The whole old row at the selected endpoint, naturally along every exact cut arrow. -/
def endpointRows : degrees F j ⋙ std ⟶ (Functor.const (Index F j)).obj (row W ⦋0⦌) where
  app a := oldVertexRow (L := L) a.1 a.2.val
  naturality a b f := by
    change std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map f.val) ≫
      oldVertexRow (L := L) b.1 b.2.val = oldVertexRow (L := L) a.1 a.2.val ≫ 𝟙 _
    rw [Category.comp_id]
    exact oldVertexRow_map F j f.val a.2.val b.2.val a.2.property b.2.property (cut_map F j f)

/-- The relative face at every original cut is exactly the constant joint row. -/
theorem supported_endpoint (a : Index F j) :
    std.map ((incl F j).app a) ≫ (endpointRows F j).app a =
      term (std.obj ((supports F j).obj a)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) :=
  oldVertexRow_supported_joint F a.1 j a.2.val a.2.property

/-- Each of the natural relative face inclusions is a monomorphism. -/
theorem incl_mono (a : Index F j) : Mono ((incl F j).app a) :=
  usedInclusion_mono F a.1 j a.2.val a.2.property

end
end DaggerModels.PartII.JTExactlyMarkedSourceDiagram
