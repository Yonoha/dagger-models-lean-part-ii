import DaggerModelsPartII.EndpointCobaseReedy
import DaggerModelsPartII.JTEndpointCobaseAugmentations
import DaggerModelsPartII.ArrowReedyCornerInterchange

/-!
# The actual zero-fixed endpoint frames under the ordered boundary

The checked projective Arrow matching corners give the relative Reedy
cofibrations of the source-to-target maps of QG and QX. Their actual
augmentations then produce Reedy cofibrant endpoint cobases under the
literal boundary, with weak maps to the original interval under that
boundary. All degrees, including degree zero, are retained.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointFrames

open JTRelativeReedyFrame JTEndpointArrowReplacement JTEndpointAugmentations
open JTEndpointCobaseAugmentations JTEndpointObjects JTEndpointCofibrancy
open ArrowReedyCornerInterchange

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance
private local instance : ModelCategory (Under Bdagger) :=
  JTEndpointCobase.underModel Bdagger
private local instance : ModelCategory (Under Bdagger)ᵒᵖ := inferInstance
private local instance : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ) :=
  simplicialReedyModelCategory (Under Bdagger)ᵒᵖ

private theorem QG_structure_relative :
    reedyMatchingProperty (fibrations Coefficientᵒᵖ)
      (NatTrans.op (structureMap QG)) := by
  intro n
  rw [fibrations_op]
  change cofibrations Coefficient
    ((relativeMatchingMap n (structureOpp QGop)).unop)
  exact ArrowReedyCornerInterchange.Actual.QG_relativeCofibration n

private theorem QX_structure_relative :
    reedyMatchingProperty (fibrations Coefficientᵒᵖ)
      (NatTrans.op (structureMap QX)) := by
  intro n
  rw [fibrations_op]
  change cofibrations Coefficient
    ((relativeMatchingMap n (structureOpp QXop)).unop)
  exact ArrowReedyCornerInterchange.Actual.QX_relativeCofibration n

private theorem QG_structure_cof (k : SimplexCategory) :
    cofibrations Coefficient ((structureMap QG).app k) := by
  induction k using SimplexCategory.rec with | h n =>
    have h : fibrations Coefficientᵒᵖ
        ((NatTrans.op (structureMap QG)).app (op ⦋n⦌)) :=
      reedyMatchingFibration_eval (NatTrans.op (structureMap QG))
        QG_structure_relative n
    rw [fibrations_op] at h
    simpa only [NatTrans.op_app, Quiver.Hom.unop_op] using h

private theorem QX_structure_cof (k : SimplexCategory) :
    cofibrations Coefficient ((structureMap QX).app k) := by
  induction k using SimplexCategory.rec with | h n =>
    have h : fibrations Coefficientᵒᵖ
        ((NatTrans.op (structureMap QX)).app (op ⦋n⦌)) :=
      reedyMatchingFibration_eval (NatTrans.op (structureMap QX))
        QX_structure_relative n
    rw [fibrations_op] at h
    simpa only [NatTrans.op_app, Quiver.Hom.unop_op] using h

private theorem QG_sourceAug_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((sourceAug QGaugmentation).app k) := by
  induction k using SimplexCategory.rec with | h n =>
    exact (QGaugmentation_weak n).1

private theorem QG_targetAug_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((targetAug QGaugmentation).app k) := by
  induction k using SimplexCategory.rec with | h n =>
    exact (QGaugmentation_weak n).2

private theorem QX_sourceAug_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((sourceAug QXaugmentation).app k) := by
  induction k using SimplexCategory.rec with | h n =>
    exact (QXaugmentation_weak n).1

private theorem QX_targetAug_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((targetAug QXaugmentation).app k) := by
  induction k using SimplexCategory.rec with | h n =>
    exact (QXaugmentation_weak n).2

/-- The actual QG endpoint cobase as a diagram under the original boundary. -/
def QGFrame : SimplexCategory ⥤ Under Bdagger :=
  underDiagram QGaugmentation

/-- The actual QX endpoint cobase as a diagram under the same boundary. -/
def QXFrame : SimplexCategory ⥤ Under Bdagger :=
  underDiagram QXaugmentation

/-- The original QG replacement gives a Reedy cofibrant under-boundary
frame in the native opposite Reedy model. -/
theorem QGFrame_reedyCofibrant : IsFibrant QGFrame.op := by
  exact EndpointCobaseReedy.endpointCobase_reedyCofibrant
    (structureMap QG) Bdagger (sourceAug QGaugmentation)
    QG_structure_relative

/-- The original QX replacement gives the same relative Reedy cofibrancy. -/
theorem QXFrame_reedyCofibrant : IsFibrant QXFrame.op := by
  exact EndpointCobaseReedy.endpointCobase_reedyCofibrant
    (structureMap QX) Bdagger (sourceAug QXaugmentation)
    QX_structure_relative

/-- The actual QG frame augmentation under the fixed original boundary. -/
def QGFrameAugmentation :
    QGFrame ⟶ (Functor.const SimplexCategory).obj (Under.mk iota) :=
  underAugmentation QGaugmentation

/-- The actual QX frame augmentation under the same original boundary. -/
def QXFrameAugmentation :
    QXFrame ⟶ (Functor.const SimplexCategory).obj (Under.mk iota) :=
  underAugmentation QXaugmentation

/-- Each component of the actual QG under-boundary augmentation is weak. -/
theorem QGFrameAugmentation_weak (k : SimplexCategory) :
    weakEquivalences (Under Bdagger) (QGFrameAugmentation.app k) := by
  change weakEquivalences Coefficient
    ((cobaseAug QGaugmentation).app k)
  exact cobaseAug_weak QGaugmentation QG_structure_cof
    QG_sourceAug_weak QG_targetAug_weak k

/-- Each component of the actual QX under-boundary augmentation is weak. -/
theorem QXFrameAugmentation_weak (k : SimplexCategory) :
    weakEquivalences (Under Bdagger) (QXFrameAugmentation.app k) := by
  change weakEquivalences Coefficient
    ((cobaseAug QXaugmentation).app k)
  exact cobaseAug_weak QXaugmentation QX_structure_cof
    QX_sourceAug_weak QX_targetAug_weak k

end

end DaggerModels.PartII.JTEndpointFrames
