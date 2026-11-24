import DaggerModelsPartII.JTIndependentTargetResolutions

/-! Assemble independent graph resolutions over the actual beads of a finite target. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace NecklaceCode DaggerSSetGluing

namespace DaggerModels.PartII.JTIndependentBeadRecursion

open JTProjectiveOrderedFiberComparison (row)
open JTFiniteNecklaceGraphRefinement (atRaw)
open JTIndependentTargetResolutions (Resolution)
open DaggerOriginalFlagFlankification

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Native (W : Source) (x y : Vertex W) :=
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)

variable {W : Source} {x y : Vertex W} (R : Native W x y)

/-- Independent graph resolutions of the initial point and each actual bead. -/
structure BeadResolutions where
  initial : ∀ {b : Vertex W} (hb : jointVertex R 0 = rawVertex W b),
    Nonempty (Resolution (atRaw (orderedPrefix R 0 (Nat.zero_le _)).source
      (jointVertex_first R) hb))
  bead : ∀ (i : Fin (beadCount R.code)) {a b : Vertex W}
    (ha : jointVertex R i.castSucc = rawVertex W a)
    (hb : jointVertex R i.succ = rawVertex W b),
    Nonempty (Resolution (atRaw (sourceBeadOver R (jointBead R.code i)) ha hb))

private theorem prefix_nonempty (F : BeadResolutions R)
    (n : ℕ) (hn : n ≤ beadCount R.code)
    {b : Vertex W} (hb : jointVertex R ⟨n, Nat.lt_succ_of_le hn⟩ = rawVertex W b) :
    Nonempty (Resolution
      (atRaw (orderedPrefix R n hn).source (jointVertex_first R) hb)) := by
  induction n generalizing b with
  | zero => exact F.initial hb
  | succ n ih =>
    let i : Fin (beadCount R.code) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    let u := jointVertex R i.castSucc
    let e := JTRawVertexRecovery.zeroVertexEquiv (JTReversalInput.ordinaryInput.obj W)
    let z : Vertex W := e.symm u
    have hz : u = rawVertex W z := (e.apply_symm_apply u).symm
    obtain ⟨L⟩ := ih (Nat.le_of_succ_le hn) hz
    obtain ⟨G⟩ := F.bead i hz hb
    exact ⟨L.join G⟩

/-- Join the independent resolutions over precisely the original finite target. -/
theorem finite_resolution_nonempty (F : BeadResolutions R) : Nonempty (Resolution R) := by
  obtain ⟨G⟩ := prefix_nonempty R F (beadCount R.code) le_rfl (jointVertex_last R)
  let G' : Resolution (assembledSource R) := G
  exact ⟨G'.postcomp (sourceAssemblyIso R).hom⟩

/-- Graph refinement gives separate resolutions for the point and actual beads. -/
def beadResolutions
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    BeadResolutions R where
  initial := by
    intro b hb
    obtain ⟨U⟩ := JTFiniteNecklaceGraphRefinement.targetComma_nonempty W hW x b
      (atRaw (orderedPrefix R 0 (Nat.zero_le _)).source (jointVertex_first R) hb)
    exact ⟨Resolution.ofGraph U⟩
  bead := by
    intro i a b ha hb
    obtain ⟨U⟩ := JTFiniteNecklaceGraphRefinement.targetComma_nonempty W hW a b
      (atRaw (sourceBeadOver R (jointBead R.code i)) ha hb)
    exact ⟨Resolution.ofGraph U⟩

/-- The initial point and each actual bead independently produce a resolution
whose complete map remains over the original finite target. -/
theorem resolution_nonempty
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    Nonempty (Resolution R) :=
  finite_resolution_nonempty R (beadResolutions R hW)

end

end DaggerModels.PartII.JTIndependentBeadRecursion
