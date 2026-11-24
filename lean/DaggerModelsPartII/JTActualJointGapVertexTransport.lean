import DaggerModelsPartII.JTExactlyMarkedSourceDiagram
import DaggerModelsPartII.JTJointOverlapPrismDiagram
import DaggerModelsPartII.JTActualSourceJointSupportTransport

/-!
The entire actual joint inverse interval retains every original source arrow.
Its selected lifted vertex is transported exactly, although interval endpoints
need not be preserved. This supplies the pointed arbitrary simplicial maps used
for incident-bead images; no flanked or endpoint-preserving flag is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointGapVertexTransport

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev zero := op (⦋0⦌ : SimplexCategory)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTExactlyMarkedSourceDiagram.Index F j

/-- The original full inverse interval over the chosen target joint. -/
abbrev gap (p : I F j) :=
  JTTargetIntervalPullback.sourceInterval (F.collapse.app p.1) j j le_rfl

/-- Every original operator acts on the WHOLE joint inverse interval. -/
abbrev overlap : I F j ⥤ SSet.{0} :=
  JTExactlyMarkedSourceDiagram.base F j ⋙ JTJointOverlapPrismDiagram.overlapSimplices F j

/-- The existing full inverse-interval inclusion in the unchanged original source. -/
abbrev inclusion (p : I F j) :=
  JTTargetIntervalGluing.middleInclusion (F.collapse.app p.1) j

/-- Actual gap transport retains the exact original native square. -/
theorem map_fac {p q : I F j} (f : p ⟶ q) :
    (overlap F j).map f ≫ inclusion F j q =
      inclusion F j p ≫ ((codes L).map f.val).map :=
  JTTargetIntervalPullback.sourceMap_fac (F.collapse.app p.1) j j le_rfl
    ((JTJointRelativeGraphFamily.native F).map f.val).left
    (Over.w ((JTJointRelativeGraphFamily.native F).map f.val))

/-- The existing lifted overlap vertex of the actual selected original cut. -/
abbrev liftedVertex (p : I F j) :=
  JTActualSourceJointSupport.liftedOverlapVertex F p.1 j p.2.val p.2.property

/-- Its canonical finite ordinal coordinate in the actual inverse interval. -/
def coordinate (p : I F j) : Fin ((gap F j p).len + 1) :=
  ((gap F j p).verticesEquiv (liftedVertex F j p)).down

/-- Every original exact-cut arrow carries the actual lifted overlap vertex exactly. -/
theorem liftedVertex_map {p q : I F j} (f : p ⟶ q) :
    ((overlap F j).map f).app zero (liftedVertex F j p) = liftedVertex F j q := by
  haveI : Mono (inclusion F j q) := by
    dsimp only [inclusion, JTTargetIntervalGluing.middleInclusion,
      JTTargetIntervalPullback.sourceInclusion]
    infer_instance
  apply (mono_iff_injective ((inclusion F j q).app zero)).mp inferInstance
  have hs := congrFun (NatTrans.congr_app (map_fac F j f) zero) (liftedVertex F j p)
  change (inclusion F j q).app zero
      (((overlap F j).map f).app zero (liftedVertex F j p)) =
    ((codes L).map f.val).map.app zero
      ((inclusion F j p).app zero (liftedVertex F j p)) at hs
  rw [JTActualSourceJointSupport.liftedOverlapVertex_fac] at hs
  rw [JTActualSourceJointSupport.liftedOverlapVertex_fac]
  exact hs.trans (DaggerOriginalProductGadget.necklaceMap_vertex_of_order
    ((codes L).map f.val).map p.2.val q.2.val
    (JTExactlyMarkedSourceDiagram.cut_map F j f))

/-- The actual gap-coordinate transport, including collapsed beads and interior joint images. -/
theorem coordinate_map {p q : I F j} (f : p ⟶ q) :
    orderMap ((overlap F j).map f) (coordinate F j p) = coordinate F j q := by
  change (((gap F j q).verticesEquiv
    (((overlap F j).map f).app zero
      ((gap F j p).verticesEquiv.symm
        (ULift.up (((gap F j p).verticesEquiv (liftedVertex F j p)).down))))).down) = _
  have he : ULift.up (((gap F j p).verticesEquiv (liftedVertex F j p)).down) =
      (gap F j p).verticesEquiv (liftedVertex F j p) := rfl
  rw [he, Equiv.symm_apply_apply, liftedVertex_map]
  rfl

end
end DaggerModels.PartII.JTActualJointGapVertexTransport
