import DaggerModelsPartII.JTParametrizedTargetFamilyJoin
import DaggerModelsPartII.JTFiniteNecklaceGraphRefinement

/-! Gluing synchronized coherent side families over any original finite native target. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace NecklaceCode DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)

namespace DaggerModels.PartII.JTFiniteParametrizedTargetFamilies

open JTParametrizedTargetFamilies (Family Presentation evaluate presentation_point_GW)
open JTParametrizedTargetFamilyJoin (PreservesFirst PreservesLast joinedLabels
  joinedPreservesFirst joinedPreservesLast)
open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTFiniteNecklaceGraphRefinement (atRaw)
open DaggerOriginalFlagFlankification

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev I (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
private abbrev Native (W : Source) (x y : Vertex W) :=
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)

variable {A : Type} [SmallCategory A] (time : A ⥤ SimplexCategory)
variable {W : Source} {x z y : Vertex W}

/-- A coherent family on the common time index, with both coefficient
endpoint conditions required to continue gluing. -/
structure Synchronized (Q : Native W x y) where
  labels : A ⥤ I W x y
  family : Family Q labels time
  first : PreservesFirst labels
  last : PreservesLast labels

variable {time} {P : Native W x z} {Q : Native W z y}

/-- Join over the original native wedge, preserving the two outside
coefficient conditions used by the next gluing. -/
def Synchronized.join (F : Synchronized time P) (G : Synchronized time Q) :
    Synchronized time (NecklacesOver.wedge P Q) where
  labels := joinedLabels F.labels G.labels F.last G.first
  family := JTParametrizedTargetFamilyJoin.join F.labels G.labels F.last G.first F.family G.family
  first := joinedPreservesFirst F.labels G.labels F.last G.first F.first
  last := joinedPreservesLast F.labels G.labels F.last G.first G.last

variable {D D' : Native W x y}

/-- Reindex both the family and its two coefficient endpoint conditions. -/
def Synchronized.precomp {B : Type} [SmallCategory B] (F : Synchronized time D)
    (G : B ⥤ A) : Synchronized (G ⋙ time) D where
  labels := G ⋙ F.labels
  family := F.family.precomp G
  first f := F.first (G.map f)
  last f := F.last (G.map f)

/-- Retain the same coherent family after postcomposing its native collapses. -/
def Synchronized.postcomp (F : Synchronized time D) (g : D ⟶ D') :
    Synchronized time D' where
  labels := F.labels
  family := F.family.postcomp g
  first := F.first
  last := F.last

section BeadInduction

variable (R : Native W x y)
variable (C : (a b : Vertex W) → Native W a b → Type)
variable (join : ∀ {a b c : Vertex W} {V : Native W a b} {U : Native W b c},
  C a b V → C b c U → C a c (NecklacesOver.wedge V U))
variable (postcomp : ∀ {a b : Vertex W} {V U : Native W a b},
  (V ⟶ U) → C a b V → C a b U)
variable (initial : ∀ {b : Vertex W} (hb : jointVertex R 0 = rawVertex W b),
  Nonempty (C x b (atRaw (orderedPrefix R 0 (Nat.zero_le _)).source (jointVertex_first R) hb)))
variable (bead : ∀ (i : Fin (beadCount R.code)) {a b : Vertex W}
    (ha : jointVertex R i.castSucc = rawVertex W a)
    (hb : jointVertex R i.succ = rawVertex W b),
  Nonempty (C a b (atRaw (sourceBeadOver R (jointBead R.code i)) ha hb)))

include join initial bead in
private theorem prefix_nonempty
    (n : ℕ) (hn : n ≤ beadCount R.code)
    {b : Vertex W} (hb : jointVertex R ⟨n, Nat.lt_succ_of_le hn⟩ = rawVertex W b) :
    Nonempty (C x b (atRaw (orderedPrefix R n hn).source (jointVertex_first R) hb)) := by
  induction n generalizing b with
  | zero => exact initial hb
  | succ n ih =>
    let i : Fin (beadCount R.code) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    let u := jointVertex R i.castSucc
    let e := JTRawVertexRecovery.zeroVertexEquiv (JTReversalInput.ordinaryInput.obj W)
    let z : Vertex W := e.symm u
    have hz : u = rawVertex W z := (e.apply_symm_apply u).symm
    obtain ⟨L⟩ := ih (Nat.le_of_succ_le hn) hz
    obtain ⟨G⟩ := bead i hz hb
    exact ⟨join L G⟩

include join postcomp initial bead in
/-- Induct over the actual beads, using the original assembly isomorphism at the end. -/
theorem nonempty_of_beads : Nonempty (C x y R) := by
  obtain ⟨G⟩ := prefix_nonempty R C join initial bead (beadCount R.code) le_rfl
    (jointVertex_last R)
  let G' : C x y (assembledSource R) := G
  exact ⟨postcomp (sourceAssemblyIso R).hom G'⟩

end BeadInduction

variable (time)
variable (R : Native W x y)

/-- The required inputs are the initial point and the actual beads of the
given native target, all over the very same time diagram. -/
structure BeadFamilies where
  initial : ∀ {b : Vertex W} (hb : jointVertex R 0 = rawVertex W b),
    Nonempty (Synchronized time (atRaw (orderedPrefix R 0 (Nat.zero_le _)).source
      (jointVertex_first R) hb))
  bead : ∀ (i : Fin (beadCount R.code)) {a b : Vertex W}
    (ha : jointVertex R i.castSucc = rawVertex W a) (hb : jointVertex R i.succ = rawVertex W b),
    Nonempty (Synchronized time (atRaw (sourceBeadOver R (jointBead R.code i)) ha hb))

variable (F : BeadFamilies time R)

include F in
/-- Synchronized coherent input for the actual beads extends to the given
finite native target with its original map into the raw realization. -/
theorem synchronized_nonempty : Nonempty (Synchronized time R) :=
  nonempty_of_beads R (fun _ _ Q ↦ Synchronized time Q) Synchronized.join
    (fun f G ↦ G.postcomp f) F.initial F.bead

include F in
/-- A weakly contractible common index gives a weakly contractible full
presentation and an evaluation into the unchanged target comma. -/
theorem exists_evaluation (hA : GW (pointMap (nerve A))) :
    ∃ (C : Cat.{0, 0}), GW (pointMap (nerve C)) ∧ Nonempty (C ⥤ TargetComma R) := by
  obtain ⟨G⟩ := synchronized_nonempty time R F
  refine ⟨Cat.of (Presentation (L := G.labels) (time := time)), ?_, ⟨evaluate G.family⟩⟩
  exact presentation_point_GW (L := G.labels) (time := time) hA

end

end DaggerModels.PartII.JTFiniteParametrizedTargetFamilies
