import DaggerModelsPartII.JTOrdinalFaceParameterPullback
import DaggerModelsPartII.JTWhiskerEdgeGraphRaw
import DaggerModelsPartII.JTActualJointChainSideLabels

/-! The whole inverse-image identity face of each actual higher-choice chain edge. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualJointChainInverseFace

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTActualJointChoiceChainGraph (Index toOriginal toTime base chainEnding chainStarting ordinals)
open JTProjectiveOrderedFiberComparison (row)
open JTOrdinalFaceInverseImage (ordinal toFace toFace_fac)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev E := NecklaceCode.single 1

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code) (p : Index F j)

private abbrev marked :=
  (JTActualJointChoiceCover.projection F j).obj ((base F j).obj p)
private abbrev u := (JTExactlyMarkedSourceDiagram.incl F j).app (marked F j p)
private abbrev α := (toOriginal F j).app p
private abbrev hα := JTActualJointChoiceChainGraph.toOriginal_surjective F j p
private abbrev hu := SimplexCategory.mono_iff_injective.mp
  (JTExactlyMarkedSourceDiagram.incl_mono F j (marked F j p))
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- The old used coefficient face at the original selected source vertex. -/
abbrev oldFace := (JTExactlyMarkedSourceDiagram.supports F j).obj (marked F j p)

/-- Every chain vertex projecting into the old full endpoint support. -/
abbrev face := ordinal (u F j p) (α F j p)

/-- Its literal inclusion in the entire chain ordinal. -/
abbrev incl := JTOrdinalFaceInverseImage.incl (u F j p) (α F j p) (hα F j p)

/-- The full ending chain edge is the identity on this entire inverse-image face. -/
theorem ending_face : std.map (incl F j p) ≫ (chainEnding F j).app p =
    JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  JTActualJointChoicePrism.ending_chain_face F j ((base F j).obj p)
    (α F j p) ((toTime F j).app p) (incl F j p)
    (toFace (u F j p) (α F j p) (hα F j p) (hu F j p))
    (toFace_fac (u F j p) (α F j p) (hα F j p) (hu F j p)).symm

/-- The starting edge is the identity on exactly the same full inverse-image face. -/
theorem starting_face : std.map (incl F j p) ≫ (chainStarting F j).app p =
    JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  JTActualJointChoicePrism.starting_chain_face F j ((base F j).obj p)
    (α F j p) ((toTime F j).app p) (incl F j p)
    (toFace (u F j p) (α F j p) (hα F j p) (hu F j p))
    (toFace_fac (u F j p) (α F j p) (hα F j p) (hu F j p)).symm

variable {X : SSet.{0}} (h : X ⟶ E.toSSet) (θ : X ⟶ J.obj ((ordinals F j).obj p))
variable (g : X ⟶ J.obj (oldFace F j p))

/-- Every compatible ending-edge graph has the literal joint raw value in all degrees. -/
theorem ending_raw (hθ : θ ≫ J.map (α F j p) = g ≫ J.map (u F j p)) :
    lift h θ ≫ realizedLabel E.toSSet W ((ordinals F j).obj p)
        (SSet.yonedaEquiv ((chainEnding F j).app p ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) =
      h ≫ term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
  let q := JTOrdinalFaceParameterPullback.factor (u F j p) (α F j p) (hα F j p) θ g hθ
  have hq : q ≫ J.map (incl F j p) = θ :=
    JTOrdinalFaceParameterPullback.factor_incl (u F j p) (α F j p) (hα F j p) θ g hθ
  rw [← hq]
  exact JTWhiskerEdgeGraphRaw.identity_edge W (z j) (incl F j p)
    ((chainEnding F j).app p) (ending_face F j p) h q

/-- The same full graph statement holds for the actual starting edge. -/
theorem starting_raw (hθ : θ ≫ J.map (α F j p) = g ≫ J.map (u F j p)) :
    lift h θ ≫ realizedLabel E.toSSet W ((ordinals F j).obj p)
        (SSet.yonedaEquiv ((chainStarting F j).app p ≫
          TwoBeadEndpointLabel.edgeLabelFromRow W)) =
      h ≫ term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
  let q := JTOrdinalFaceParameterPullback.factor (u F j p) (α F j p) (hα F j p) θ g hθ
  have hq : q ≫ J.map (incl F j p) = θ :=
    JTOrdinalFaceParameterPullback.factor_incl (u F j p) (α F j p) (hα F j p) θ g hθ
  rw [← hq]
  exact JTWhiskerEdgeGraphRaw.identity_edge W (z j) (incl F j p)
    ((chainStarting F j).app p) (starting_face F j p) h q

end
end DaggerModels.PartII.JTActualJointChainInverseFace
