import DaggerModelsPartII.JTJointPairGapChainLabels
import DaggerModelsPartII.JTJointSideWhiskerParameterTransport

/-! The full original-time parameter on both added edges and the old gap. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointPairGapChainParameter

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

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
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointPairChainDiagram.Index F j
private abbrev pair (p : I F j) := (JTJointPairGapChainLabels.oldPairs F j).obj p
private abbrev a (p : I F j) := (JTJointPairSourceDiagram.base F j).obj (pair F j p)
private abbrev v (p : I F j) := (pair F j p).2.left.val
private abbrev w (p : I F j) := (pair F j p).2.right.val
private abbrev h (p : I F j) := (pair F j p).2.le
private abbrev B (p : I F j) := JTJointPairGapDiagram.code F j (pair F j p)
private abbrev T (p : I F j) := J.obj (time.obj (a F j p))
private abbrev K (p : I F j) :=
  J.obj ((JTJointPairChainDiagram.coefficient F j).obj ((JTJointPairChainDiagram.base F j).obj p))

/-- The unchanged whole interval and the original time on common pair chains. -/
abbrev oldParameter (p : I F j) : (B F j p).toSSet ⊗ T F j p ⟶ K F j p :=
  JTJointPairGapDiagram.parameter F j (pair F j p)

/-- The complete original time functor on the simultaneous higher choices. -/
abbrev oldTime : I F j ⥤ SimplexCategory :=
  JTJointPairGapChainLabels.oldPairs F j ⋙ JTJointPairSourceDiagram.base F j ⋙ time

/-- The original coefficient degree retained beneath the common chain. -/
abbrev oldDegrees : I F j ⥤ SimplexCategory :=
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChainDiagram.coefficient F j

/-- The original full interval parameter respects every pair-preserving arrow. -/
theorem oldParameter_map {p q : I F j} (f : p ⟶ q) :
    (((JTJointPairGapChainLabels.oldNative F j).map f).map ⊗ₘ
      J.map ((oldTime F j).map f)) ≫ oldParameter F j q =
      oldParameter F j p ≫ J.map ((oldDegrees F j).map f) :=
  JTJointPairGapDiagram.parameter_map F j
    ((JTJointPairGapChainLabels.oldPairs F j).map f)

/-- Append the later relative edge, then prepend the earlier one. -/
def parameter (p : I F j) :
    (JTJointPairGapChainLabels.code F j p).toSSet ⊗ T F j p ⟶ K F j p :=
  JTJointSideWhisker.prependParameter
    (JTJointSideWhisker.appendParameter (oldParameter F j p))

/-- The padded full-time parameter is natural in all simultaneous chain arrows. -/
theorem parameter_map {p q : I F j} (f : p ⟶ q) :
    ((JTJointPairGapChainLabels.codeMap F j f).map ⊗ₘ
      J.map ((oldTime F j).map f)) ≫ parameter F j q =
      parameter F j p ≫ J.map ((oldDegrees F j).map f) := by
  let g := (JTJointPairGapChainLabels.oldNative F j).map f
  let u := J.map ((oldTime F j).map f)
  let r := (oldDegrees F j).map f
  have hg := oldParameter_map F j f
  have ha := JTJointSideWhiskerParameterTransport.append_map g u r
    (oldParameter F j p) (oldParameter F j q) hg
  have hp := JTJointSideWhiskerParameterTransport.prepend_map
    (wedgeMap g (𝟙 E)) u r
    (JTJointSideWhisker.appendParameter (oldParameter F j p))
    (JTJointSideWhisker.appendParameter (oldParameter F j q)) ha
  exact hp

/-- The padded native codes with the complete original groupoid time. -/
abbrev X : I F j ⥤ SSet.{0} :=
  (((JTJointPairGapChainLabels.native F j) ⋙ NecklaceCode.simplicialFunctor).prod'
    ((oldTime F j) ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}

/-- The full old-degree parameter on every object and every chain arrow. -/
def coarseParameter : X F j ⟶ oldDegrees F j ⋙ J where
  app := parameter F j
  naturality _ _ f := parameter_map F j f

/-- The whole old timed gap is retained inside the padded prism. -/
theorem parameter_interior (p : I F j) :
    (JTJointPairGapChainLabels.interiorInclusion F j p ⊗ₘ 𝟙 (T F j p)) ≫
      parameter F j p = oldParameter F j p := by
  unfold parameter
  change ((wedgeιLeft (B F j p) E ≫
      wedgeιRight E (wedge (B F j p) E)) ⊗ₘ 𝟙 (T F j p)) ≫
        JTJointSideWhisker.prependParameter
          (JTJointSideWhisker.appendParameter (oldParameter F j p)) = _
  rw [← Category.id_comp (𝟙 (T F j p)), ← tensorHom_comp_tensorHom,
    Category.assoc, JTJointSideWhisker.prependParameter_interior,
    JTJointSideWhisker.appendParameter_interior]

/-- The first old gap trace is the earlier cut's complete time parameter. -/
theorem old_firstTrace (p : I F j) :
    (pointAt (B F j p) (ULift.up 0) ⊗ₘ 𝟙 (T F j p)) ≫ oldParameter F j p =
      JTActualSourceJointSupport.timeParameter F (a F j p) (v F j p) :=
  JTActualJointGapPrism.parameter_first F (a F j p)
    (v F j p) (w F j p) (h F j p)

/-- The last old gap trace is the later cut's complete time parameter. -/
theorem old_lastTrace (p : I F j) :
    (pointAt (B F j p) (ULift.up (Fin.last (B F j p).len)) ⊗ₘ
      𝟙 (T F j p)) ≫ oldParameter F j p =
        JTActualSourceJointSupport.timeParameter F (a F j p) (w F j p) :=
  JTActualJointGapPrism.parameter_last F (a F j p)
    (v F j p) (w F j p) (h F j p)

private theorem appended_firstTrace (p : I F j) :
    (pointAt (wedge (B F j p) E) (ULift.up 0) ⊗ₘ 𝟙 (T F j p)) ≫
      JTJointSideWhisker.appendParameter (oldParameter F j p) =
        (pointAt (B F j p) (ULift.up 0) ⊗ₘ 𝟙 (T F j p)) ≫
          oldParameter F j p := by
  rw [← pointAt_first_left (B F j p) E]
  rw [← Category.id_comp (𝟙 (T F j p)), ← tensorHom_comp_tensorHom,
    Category.assoc, JTJointSideWhisker.appendParameter_interior]
  simp only [Category.comp_id]

/-- The prepended edge uses the earlier cut's complete original time trace. -/
theorem parameter_front (p : I F j) :
    (JTJointPairGapChainLabels.frontInclusion F j p ⊗ₘ 𝟙 (T F j p)) ≫
      parameter F j p =
        JTJointSideWhisker.edgeParameter
          (JTActualSourceJointSupport.timeParameter F (a F j p) (v F j p)) := by
  unfold parameter JTJointSideWhisker.prependParameter
  rw [JTComposedPrismLabels.parameter_left]
  change JTJointSideWhisker.edgeParameter
    ((pointAt (wedge (B F j p) E) (ULift.up 0) ⊗ₘ 𝟙 (T F j p)) ≫
      JTJointSideWhisker.appendParameter (oldParameter F j p)) = _
  rw [appended_firstTrace, old_firstTrace]

/-- The appended edge uses the later cut's complete original time trace. -/
theorem parameter_back (p : I F j) :
    (JTJointPairGapChainLabels.backInclusion F j p ⊗ₘ 𝟙 (T F j p)) ≫
      parameter F j p =
        JTJointSideWhisker.edgeParameter
          (JTActualSourceJointSupport.timeParameter F (a F j p) (w F j p)) := by
  unfold parameter
  change ((wedgeιRight (B F j p) E ≫
      wedgeιRight E (wedge (B F j p) E)) ⊗ₘ 𝟙 (T F j p)) ≫
        JTJointSideWhisker.prependParameter
          (JTJointSideWhisker.appendParameter (oldParameter F j p)) = _
  rw [← Category.id_comp (𝟙 (T F j p)), ← tensorHom_comp_tensorHom,
    Category.assoc, JTJointSideWhisker.prependParameter_interior]
  unfold JTJointSideWhisker.appendParameter
  rw [JTComposedPrismLabels.parameter_right]
  change JTJointSideWhisker.edgeParameter
    ((pointAt (B F j p) (ULift.up (Fin.last (B F j p).len)) ⊗ₘ
      𝟙 (T F j p)) ≫ oldParameter F j p) = _
  rw [old_lastTrace]

end
end DaggerModels.PartII.JTJointPairGapChainParameter
