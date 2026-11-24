import DaggerModelsPartII.JTRigidJointGraphCover
import DaggerModelsPartII.JTWeakCoveredPushout

/-! Stitch the exact covered graphs over a target joint by a weak pushout. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels MonoidalCategory
open MorphismProperty CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRigidJointGraphGluing

open JTJointRelativeParameters (withTime withTimeMap withTimeMap_app underlying_isPushout)
open JTJointRelativeGraphFamily (native coefficient leftLeg rightLeg RawOn)
open JTParametrizedTargetFamilies (Family codes)
open JTTargetIntervalOverMapping (left right whole overlapToLeft)
open JTTargetJointMarks (Joint)
open JTRigidOverlapDiagram (CommonCover)
open JTRigidJointGraphCover (overlapData coveredLeft coveredRight coveredSides_parameter_agree)
open JTNecklaceEndpointCylinder (cylinder)
open DecoratedCylinderNecklacePresentation (underCocone)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (C : CommonCover (overlapData F j s t))

private abbrev leftSide := coveredLeft F j s t C
private abbrev rightSide := coveredRight F j s t C
private abbrev allSource := withTime Q.map J time (native F) (whole Q.code)

private abbrev lower := underlying_isPushout Q J time (native F) j

/-- Glue the two covered sides along their common coefficient trace. -/
abbrev assembledSource := JTWeakCoveredPushout.source
  (leftSide F j s t C).fromOverlap (rightSide F j s t C).fromOverlap

/-- The glued source projects naturally to the entire original source diagram. -/
def projection : assembledSource F j s t C ⟶ allSource F :=
  JTWeakCoveredPushout.projection (lower F j)
    (leftSide F j s t C).fromOverlap (rightSide F j s t C).fromOverlap
    C.projection (leftSide F j s t C).projection (rightSide F j s t C).projection
    (leftSide F j s t C).projectsOverlap (rightSide F j s t C).projectsOverlap

/-- The common overlap restriction gives a parameter on the glued source. -/
def parameter : assembledSource F j s t C ⟶ coefficient (L := L) ⋙ J :=
  JTWeakCoveredPushout.parameter
    (leftSide F j s t C).fromOverlap (rightSide F j s t C).fromOverlap
    (leftSide F j s t C).parameter (rightSide F j s t C).parameter
    (coveredSides_parameter_agree F j s t C)

private theorem mono_tensor_id {S T : SSet.{0}} (i : S ⟶ T) (K : SSet.{0})
    (hi : Mono i) : Mono (i ⊗ₘ 𝟙 K) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro d
  apply (mono_iff_injective _).mpr
  intro z z' h
  change (i.app d z.1, z.2) = (i.app d z'.1, z'.2) at h
  have inj := (mono_iff_injective (i.app d)).mp ((NatTrans.mono_iff_mono_app _).mp hi d)
  have hfst : i.app d z.1 = i.app d z'.1 := congrArg Prod.fst h
  have hsnd : z.2 = z'.2 := congrArg (@Prod.snd (T.obj d) (K.obj d)) h
  exact Prod.ext (inj hfst) hsnd

set_option maxHeartbeats 800000 in
private theorem overlapLeft_mono :
    Mono (withTimeMap Q.map J time (native F) (overlapToLeft Q.code j)) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro p
  rw [withTimeMap_app]
  let P := (native F).obj p
  let a := ((overlapToLeft Q.code j).app P).left
  haveI : Mono (JTTargetIntervalGluing.middleInclusion P.hom j) := by
    unfold JTTargetIntervalGluing.middleInclusion JTTargetIntervalPullback.sourceInclusion
    infer_instance
  have hma : Mono a := mono_of_mono_fac (JTTargetIntervalGluing.middleLeft_fac P.hom j)
  exact mono_tensor_id a _ hma

private theorem weak_of_trivial {A B : SSet.{0}} (f : A ⟶ B)
    (h : trivialFibrations SSet.{0} f) : weakEquivalences SSet.{0} f :=
  (weakEquivalence_iff _).mp ((mem_trivialFibrations_iff _).mp h).2

private theorem coveredProjection_weak {D : JTRigidOverlapDiagram.Data I}
    {C' : CommonCover D} {P : I ⥤ SSet.{0}} {l : D.left ⟶ P} {r : D.right ⟶ P}
    (sq : IsPushout D.leftInclusion D.rightInclusion l r)
    (A : JTRigidJointGraphCover.CoveredSide C' D.left D.leftInclusion D.leftReference
      D.leftCode D.leftNative)
    (B : JTRigidJointGraphCover.CoveredSide C' D.right D.rightInclusion D.rightReference
      D.rightCode D.rightNative)
    [Mono D.leftInclusion] (p : I) :
    weakEquivalences SSet.{0}
      ((JTWeakCoveredPushout.projection sq A.fromOverlap B.fromOverlap
        C'.projection A.projection B.projection A.projectsOverlap B.projectsOverlap).app p) :=
  JTWeakCoveredPushout.projection_weak sq A.fromOverlap B.fromOverlap
    C'.projection A.projection B.projection A.projectsOverlap B.projectsOverlap
    (fun q ↦ weak_of_trivial _ (C'.trivialFibration q))
    (fun q ↦ weak_of_trivial _ (A.trivialFibration q))
    (fun q ↦ weak_of_trivial _ (B.trivialFibration q)) p

set_option maxHeartbeats 800000 in
/-- Gluing the exact side graphs preserves the weak type of the original source. -/
theorem projection_weak (p : I) :
    weakEquivalences SSet.{0} ((projection F j s t C).app p) := by
  letI h : Mono (overlapData F j s t).leftInclusion := overlapLeft_mono F j
  exact coveredProjection_weak (D := overlapData F j s t) (C' := C) (lower F j)
    (leftSide F j s t C) (rightSide F j s t C) p

end

end DaggerModels.PartII.JTRigidJointGraphGluing
