import DaggerModelsPartII.JTSupportedNormalizedLabel
import DaggerModelsPartII.JTComposedPrismLabelSingleton
import DaggerModelsPartII.JTParametrizedTargetFamilyComparison
import DaggerModelsPartII.JTJointTraceObstruction

/-! Compare every internal necklace of a supported normalized time prism. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSupportedNormalizedEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (Family evaluate)
open JTConstantOrderedLabel (constantIndex)
open JTSupportedNormalizedLabel (Data coefficients fromSupported coefficient_onFace)
open JTPointTargetEvaluationCone (pointTarget pointLabel center)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter
private abbrev one := Discrete PUnit
private abbrev E := single 1
private abbrev code (T : NecklaceCode) := wedge E (wedge T E)

variable {W : Source} {T : NecklaceCode} {k l n : SimplexCategory} {z : Vertex W}
variable (D : Data W T k z) (u : l ⟶ k)
variable (hm : std.map u ≫ D.middle = JTConstantOrderedLabel.constantCoefficient W z T l)
variable (hf : std.map u ≫ D.front = JTConstantOrderedLabel.constantCoefficient W z E l)
variable (hb : std.map u ≫ D.back = JTConstantOrderedLabel.constantCoefficient W z E l)
variable (p : (code T).toSSet ⊗ J.obj n ⟶ J.obj l)

/-- Constant labels on the original normalized native triple, at the used degree. -/
abbrev supportedLabels := (Functor.const one).obj (constantIndex W z (code T) l)

/-- The full original-degree normalized label, without replacing its coefficient. -/
abbrev normalizedLabels := (Functor.const one).obj (JTComposedPrismLabels.index (coefficients D))

private abbrev time := (Functor.const one).obj n

/-- The supported full-time prism as a genuine point-target family. -/
def supportedFamily : Family (pointTarget W z)
    (supportedLabels (W := W) (T := T) (l := l) (z := z)) (time (n := n)) where
  collapse := {
    app := fun _ ↦ JTOrderedLabelJointInsertion.toPoint (code T)
    naturality := by intros; simp }
  parameter _ := p
  parameter_map := by
    intro a b f
    have hab : a = b := Subsingleton.elim _ _
    subst b
    have hfid : f = 𝟙 a := Subsingleton.elim _ _
    subst f
    simp
    change (𝟙 (code T).toSSet ▷ J.obj n) ≫ p = p
    rw [id_whiskerRight, Category.id_comp]
  raw _ := JTJointTraceObstruction.constant_raw_overPoint W z (code T) l n p

include hm hf hb in
private theorem normalized_raw :
    JTComposedPrismLabels.rawProduct W (p ≫ J.map u)
      (JTComposedPrismLabels.coefficient (coefficients D)) =
      fst (code T).toSSet (J.obj n) ≫
        (JTOrderedLabelJointInsertion.toPoint (code T)).map ≫ (pointTarget W z).map := by
  rw [JTComposedPrismLabels.rawProduct_coefficient, coefficient_onFace D u hm hf hb,
    JTComposedPrismLabels.rawProduct_constant]
  have ht : (JTOrderedLabelJointInsertion.toPoint (code T)).map = term (code T).toSSet :=
    JTOrderedLabelJointInsertion.pointIsTerminal.hom_ext _ _
  rw [ht]
  rfl

/-- The original-degree normalized family carries the parameter through its
actual used-face inclusion, over the same literal raw joint point. -/
def normalizedFamily : Family (pointTarget W z) (normalizedLabels D) (time (n := n)) :=
  JTComposedPrismLabelSingleton.family (pointTarget W z) (coefficients D)
    (JTOrderedLabelJointInsertion.toPoint _) (p ≫ J.map u) (normalized_raw D u hm hf hb p)

/-- The actual supported decorated arrow, retaining the entire normalized code. -/
def labelsComparison : supportedLabels (W := W) (T := T) (l := l) (z := z) ⟶
    normalizedLabels D where
  app _ := fromSupported D u hm hf hb
  naturality := by intros; simp

private theorem compatible : JTParametrizedTargetFamilyComparison.Compatible
    (labelsComparison D u hm hf hb) (𝟙 (time (n := n)))
    (supportedFamily p) (normalizedFamily D u hm hf hb p) where
  collapse := by
    apply NatTrans.ext
    funext a
    change (𝟙 (code T)) ≫ JTOrderedLabelJointInsertion.toPoint _ =
      JTOrderedLabelJointInsertion.toPoint _
    rw [Category.id_comp]
  parameter _ := by
    change (𝟙 (code T).toSSet ⊗ₘ J.map (𝟙 n)) ≫ (p ≫ J.map u) = p ≫ J.map u
    rw [J.map_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- The comparison acts on all internal necklaces, not only on the displayed bead. -/
abbrev presentation := JTParametrizedTargetFamilyComparison.presentation
  (labelsComparison D u hm hf hb) (𝟙 (time (n := n)))

/-- The actual natural transformation between the full fixed-point evaluations. -/
def compare : evaluate (supportedFamily p) ⟶
    presentation D u hm hf hb ⋙ evaluate (normalizedFamily D u hm hf hb p) :=
  JTParametrizedTargetFamilyComparison.compare (labelsComparison D u hm hf hb)
    (𝟙 _) (supportedFamily p) (normalizedFamily D u hm hf hb p)
    (compatible D u hm hf hb p)

/-- The comparison of complete internal-necklace presentations is nerve weak. -/
theorem presentation_weak : HomotopicalAlgebra.WeakEquivalence
    (nerveMap (presentation (n := n) D u hm hf hb)) :=
  JTParametrizedTargetFamilyComparison.presentation_weak
    (labelsComparison D u hm hf hb) (𝟙 (time (n := n)))

private def toPoint : supportedLabels (W := W) (T := T) (l := l) (z := z) ⟶
    (Functor.const one).obj (pointLabel W z) where
  app _ := JTSupportedNormalizedLabel.supportedToPoint
  naturality := by intros; simp

/-- The same full supported evaluation also has its actual cone to the
canonical center of the unchanged point-target comma category. -/
def evaluation_toPoint : evaluate (supportedFamily p) ⟶
    (Functor.const _).obj (center W z) :=
  JTPointTargetEvaluationCone.evaluation_toPoint W z (supportedFamily p)
    (toPoint (W := W) (T := T) (l := l) (z := z))

end
end DaggerModels.PartII.JTSupportedNormalizedEvaluation
