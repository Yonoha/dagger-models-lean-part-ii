import DaggerModelsPartII.JTJointBeadSupportedNormalization
import DaggerModelsPartII.JTJointSideWhiskerParameterTransport
import DaggerModelsPartII.JTJointBeadOverlapRestriction

/-! Full-time supported coefficients on the padded actual joint bead. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointBeadNormalizedParameter

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedBeadGraph (fullBeadParameter fullBeadSupport
  fullBeadSupportInclusion)
open JTJointSideWhisker (appendParameter prependParameter)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ) (j : Joint Q.code)
variable (r : (single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)

private abbrev native := r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j
private abbrev k := (JTJointRelativeGraphFamily.coefficient (L := L)).obj a
private abbrev l := fullBeadSupport F a d (native F a d j r)
private abbrev incl := fullBeadSupportInclusion F a d (native F a d j r)
private abbrev bead := single d

/-- The entire old coefficient, on the native single bead and full original time. -/
def originalMiddle : (bead d).toSSet ⊗ J.obj (time.obj a) ⟶ J.obj (k (L := L) a) :=
  ((singleIso d).hom ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫
    fullBeadParameter F a d (native F a d j r)

/-- The supported coefficient on the same native bead and the same full time. -/
def supportedMiddle : (bead d).toSSet ⊗ J.obj (time.obj a) ⟶ J.obj (l F a d j r) :=
  ((singleIso d).hom ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫
    JTPrismRectangle.supportedParameter
      (fullBeadParameter F a d (native F a d j r))

/-- Support inclusion recovers the original full-time middle parameter. -/
theorem supportedMiddle_fac :
    supportedMiddle F a d j r ≫ J.map (incl F a d j r) =
      originalMiddle F a d j r := by
  unfold supportedMiddle originalMiddle
  rw [Category.assoc, JTPrismRectangle.supportedParameter_factor]

/-- The old coefficient on the two added edges and the original middle bead. -/
def originalPadded :
    (wedge E (wedge (bead d) E)).toSSet ⊗ J.obj (time.obj a) ⟶
      J.obj (k (L := L) a) :=
  prependParameter (appendParameter (originalMiddle F a d j r))

/-- The supported coefficient on that identical full padded-time prism. -/
def supportedPadded :
    (wedge E (wedge (bead d) E)).toSSet ⊗ J.obj (time.obj a) ⟶
      J.obj (l F a d j r) :=
  prependParameter (appendParameter (supportedMiddle F a d j r))

/-- The entire padded prism factors through the actual used coefficient support. -/
theorem supportedPadded_fac :
    supportedPadded F a d j r ≫ J.map (incl F a d j r) =
      originalPadded F a d j r := by
  let p := supportedMiddle F a d j r
  let q := originalMiddle F a d j r
  have hm : p ≫ J.map (incl F a d j r) = q :=
    supportedMiddle_fac F a d j r
  have ha := JTJointSideWhiskerParameterTransport.append_map
    (𝟙 (bead d)) (𝟙 (J.obj (time.obj a))) (incl F a d j r) p q (by
      simpa only [Category.id_comp, Category.comp_id] using hm.symm)
  have hi : wedgeMap (𝟙 (bead d)) (𝟙 E) = 𝟙 (wedge (bead d) E) :=
    wedgeMap_id
  rw [hi] at ha
  have hp := JTJointSideWhiskerParameterTransport.prepend_map
    (𝟙 (wedge (bead d) E)) (𝟙 (J.obj (time.obj a))) (incl F a d j r)
    (appendParameter p) (appendParameter q) (by
      simpa using ha)
  have ho : wedgeMap (𝟙 E) (𝟙 (wedge (bead d) E)) =
      𝟙 (wedge E (wedge (bead d) E)) := wedgeMap_id
  rw [ho] at hp
  have hid : (𝟙 (wedge E (wedge (bead d) E)) :
      wedge E (wedge (bead d) E) ⟶ wedge E (wedge (bead d) E)).map =
      𝟙 (wedge E (wedge (bead d) E)).toSSet :=
    NecklaceCode.simplicialFunctor.map_id _
  rw [hid] at hp
  rw [tensorHom_id] at hp
  rw [id_whiskerRight] at hp
  rw [Category.id_comp] at hp
  simpa [supportedPadded, originalPadded]
    using hp.symm

/-- The original bead is still the complete interior of the padded prism. -/
theorem originalPadded_interior :
    ((wedgeιLeft (bead d) E ≫ wedgeιRight E (wedge (bead d) E)) ⊗ₘ
      𝟙 (J.obj (time.obj a))) ≫ originalPadded F a d j r =
        originalMiddle F a d j r := by
  unfold originalPadded
  rw [← Category.id_comp (𝟙 (J.obj (time.obj a))), ← tensorHom_comp_tensorHom,
    Category.assoc, JTJointSideWhisker.prependParameter_interior,
    JTJointSideWhisker.appendParameter_interior]

/-- Restricting the supported padded prism recovers its whole supported middle. -/
theorem supportedPadded_interior :
    ((wedgeιLeft (bead d) E ≫ wedgeιRight E (wedge (bead d) E)) ⊗ₘ
      𝟙 (J.obj (time.obj a))) ≫ supportedPadded F a d j r =
        supportedMiddle F a d j r := by
  unfold supportedPadded
  rw [← Category.id_comp (𝟙 (J.obj (time.obj a))), ← tensorHom_comp_tensorHom,
    Category.assoc, JTJointSideWhisker.prependParameter_interior,
    JTJointSideWhisker.appendParameter_interior]


end
end DaggerModels.PartII.JTJointBeadNormalizedParameter

