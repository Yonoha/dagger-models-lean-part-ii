import DaggerModelsPartII.JTMarkedParametrizedTargetFamilyJoin
import DaggerModelsPartII.JTBinaryPrismParameterBounds
import DaggerModelsPartII.JTFiniteParametrizedTargetFamilies

/-! Transported coefficient bounds allow gluing along the actual beads of a fixed target. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalFlagFlankification
open DaggerOriginalProductGadget (pointMap)

namespace DaggerModels.PartII.JTMarkedFiniteParametrizedTargetFamilies

open JTMarkedParametrizedTargetFamilyJoin (Mark LowerBound UpperBound joinedLabels leftMark rightMark)
open JTParametrizedTargetFamilies (Family Presentation evaluate presentation_point_GW)
open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTFiniteNecklaceGraphRefinement (atRaw)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Index (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
private abbrev Native (W : Source) (x y : Vertex W) :=
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)

variable {A : Type} [SmallCategory A] (time : A ⥤ SimplexCategory)
variable {W : Source} {x z y : Vertex W}

/-- A whole family over the common time with two transported bounds. -/
structure Synchronized (Q : Native W x y) where
  labels : A ⥤ Index W x y
  family : Family Q labels time
  lower : Mark labels
  upper : Mark labels
  lower_bound : LowerBound family lower
  upper_bound : UpperBound family upper

variable {time} {P : Native W x z} {Q : Native W z y}

set_option maxHeartbeats 400000 in
/-- The left lower bound and the right upper bound survive gluing over the native wedge. -/
def Synchronized.join (F : Synchronized time P) (G : Synchronized time Q) :
    Synchronized time (NecklacesOver.wedge P Q) where
  labels := joinedLabels F.labels G.labels F.upper G.lower
  family := JTMarkedParametrizedTargetFamilyJoin.join F.labels G.labels F.upper G.lower
    F.family G.family F.upper_bound G.lower_bound
  lower := leftMark F.labels G.labels F.upper G.lower F.lower
  upper := rightMark F.labels G.labels F.upper G.lower G.upper
  lower_bound p := JTBinaryPrismParameterBounds.parameter_lower_bound
    (F.family.parameter p) (G.family.parameter p) (F.lower.vertex p) (F.lower_bound p)
  upper_bound p := JTBinaryPrismParameterBounds.parameter_upper_bound
    (F.family.parameter p) (G.family.parameter p) (G.upper.vertex p) (G.upper_bound p)

variable {D D' : Native W x y}

/-- Postcompose the native collapse, leaving the coefficient bounds intact. -/
def Synchronized.postcomp (F : Synchronized time D) (g : D ⟶ D') : Synchronized time D' where
  labels := F.labels
  family := F.family.postcomp g
  lower := F.lower
  upper := F.upper
  lower_bound := F.lower_bound
  upper_bound := F.upper_bound

variable (time)
variable (Q₀ : Native W x y)

/-- Coherent marked families on the initial point and each actual bead. -/
structure BeadFamilies where
  initial : ∀ {b : Vertex W} (hb : jointVertex Q₀ 0 = rawVertex W b),
    Nonempty (Synchronized time
      (atRaw (orderedPrefix Q₀ 0 (Nat.zero_le _)).source (jointVertex_first Q₀) hb))
  bead : ∀ (i : Fin (beadCount Q₀.code)) {a b : Vertex W}
    (ha : jointVertex Q₀ i.castSucc = rawVertex W a)
    (hb : jointVertex Q₀ i.succ = rawVertex W b),
    Nonempty (Synchronized time
      (atRaw (sourceBeadOver Q₀ (jointBead Q₀.code i)) ha hb))

variable (F : BeadFamilies time Q₀)

include F in
/-- Iterate the marked gluing to the literal original target, retaining both outer bounds. -/
theorem synchronized_nonempty : Nonempty (Synchronized time Q₀) :=
  JTFiniteParametrizedTargetFamilies.nonempty_of_beads Q₀
    (fun _ _ T ↦ Synchronized time T) Synchronized.join (fun f B ↦ B.postcomp f)
    F.initial F.bead

include F in
/-- If the common index has weakly contractible nerve, so does the presentation
retaining all the internal necklaces of the glued family over the original target. -/
theorem exists_evaluation (hA : GW (pointMap (nerve A))) :
    ∃ (C : Cat.{0, 0}), GW (pointMap (nerve C)) ∧ Nonempty (C ⥤ TargetComma Q₀) := by
  obtain ⟨G⟩ := synchronized_nonempty time Q₀ F
  refine ⟨Cat.of (Presentation (L := G.labels) (time := time)), ?_, ⟨evaluate G.family⟩⟩
  exact presentation_point_GW (L := G.labels) (time := time) hA

end

end DaggerModels.PartII.JTMarkedFiniteParametrizedTargetFamilies
