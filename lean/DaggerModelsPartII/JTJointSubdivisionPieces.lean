import DaggerModelsPartII.JTJointSubdivisionInsertion
import DaggerModelsPartII.JTJointSubdivisionBeadNormalization

/-!
Both new adjacent intervals of an actual cut insertion vary functorially under
the original source operators, including coalescence. They are charts in the
same inserted cut set. These selectors do not choose or identify independent
normalization edges and do not assert normalized refinement coherence.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointSubdivisionPieces

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointSubdivisionInsertion.Index F j
private abbrev C := JTJointSubdivisionBeadCharts.Index F j
private abbrev vertices {p q : I F j} (f : p ⟶ q) :=
  orderMap ((codes L).map ((JTJointSubdivisionInsertion.base F j).map f)).map

private theorem first_map {p q : I F j} (f : p ⟶ q) :
    vertices F j f p.1.2.firstCut = q.1.2.firstCut :=
  congrArg (fun c : JTJointSubdivisionBeadCharts.Chart F j q.1.1 ↦ c.firstCut)
    f.val.property

private theorem middle_map {p q : I F j} (f : p ⟶ q) :
    vertices F j f p.2.val = q.2.val := congrArg Subtype.val f.property

private theorem last_map {p q : I F j} (f : p ⟶ q) :
    vertices F j f p.1.2.lastCut = q.1.2.lastCut :=
  congrArg (fun c : JTJointSubdivisionBeadCharts.Chart F j q.1.1 ↦ c.lastCut)
    f.val.property

/-- The whole inserted cut set transports by the literal original vertex image. -/
theorem refinedCuts_map {p q : I F j} (f : p ⟶ q) :
    JTJointPairSubdivisionDiagram.transport F j f.val.val
      (JTJointSubdivisionInsertion.refinedCuts F j p) =
        JTJointSubdivisionInsertion.refinedCuts F j q := by
  have hC := congrArg (fun c : JTJointSubdivisionBeadCharts.Chart F j q.1.1 ↦ c.cuts)
    f.val.property
  change JTJointPairSubdivisionDiagram.transport F j f.val.val p.1.2.cuts =
    q.1.2.cuts at hC
  have hv := congrArg Subtype.val hC
  apply Subtype.ext
  change (insert p.2.val p.1.2.cuts.val).image (vertices F j f) =
    insert q.2.val q.1.2.cuts.val
  rw [Finset.image_insert, middle_map F j f]
  exact congrArg (insert q.2.val) hv

private def lowerObj (p : I F j) : C F j :=
  ⟨p.1.1, ⟨JTJointSubdivisionInsertion.refinedCuts F j p,
    p.1.2.firstCut, p.2.val, JTJointSubdivisionInsertion.lower_adjacent F j p⟩⟩

private def upperObj (p : I F j) : C F j :=
  ⟨p.1.1, ⟨JTJointSubdivisionInsertion.refinedCuts F j p,
    p.2.val, p.1.2.lastCut, JTJointSubdivisionInsertion.upper_adjacent F j p⟩⟩

/-- The first new actual adjacent chart, with every original source arrow retained. -/
def lower : I F j ⥤ C F j where
  obj := lowerObj F j
  map f := ⟨f.val.val, by
    apply JTJointSubdivisionBeadCharts.Chart.ext
    · exact refinedCuts_map F j f
    · exact first_map F j f
    · exact middle_map F j f⟩
  map_id p := by apply CategoryOfElements.ext; rfl
  map_comp f g := by apply CategoryOfElements.ext; rfl

/-- The second new chart in the SAME inserted cut set, including zero length. -/
def upper : I F j ⥤ C F j where
  obj := upperObj F j
  map f := ⟨f.val.val, by
    apply JTJointSubdivisionBeadCharts.Chart.ext
    · exact refinedCuts_map F j f
    · exact middle_map F j f
    · exact last_map F j f⟩
  map_id p := by apply CategoryOfElements.ext; rfl
  map_comp f g := by apply CategoryOfElements.ext; rfl

/-- Lower chart restriction keeps the original source and operator literally. -/
theorem lower_base : lower F j ⋙ JTJointSubdivisionBeadCharts.base F j =
    JTJointSubdivisionInsertion.base F j := rfl

/-- Upper chart restriction keeps that same original source and operator. -/
theorem upper_base : upper F j ⋙ JTJointSubdivisionBeadCharts.base F j =
    JTJointSubdivisionInsertion.base F j := rfl

/-- Both new bead widths and all their original endpoint-preserving operators. -/
abbrev lowerDegrees := lower F j ⋙ JTJointSubdivisionBeadNormalization.degrees F j

/-- The full upper-bead degree diagram, without dropping coalescing operators. -/
abbrev upperDegrees := upper F j ⋙ JTJointSubdivisionBeadNormalization.degrees F j

end
end DaggerModels.PartII.JTJointSubdivisionPieces
