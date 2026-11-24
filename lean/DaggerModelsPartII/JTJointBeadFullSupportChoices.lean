import DaggerModelsPartII.JTJointBeadEndpointDiagram
import DaggerModelsPartII.JTTwoEndpointChoiceCover
import DaggerModelsPartII.JTTwoEndpointChoicePrism

/-! Full higher relative endpoint choices on the actual timed overlap bead. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointBeadFullSupportChoices

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}

variable {A B : Type} [SmallCategory A] [SmallCategory B]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (base : B ⥤ A) (D : B ⥤ SimplexCategory)
variable (h₀ : ∀ {a b : B} (f : a ⟶ b), (D.map f).toOrderHom 0 = 0)
variable (h₁ : ∀ {a b : B} (f : a ⟶ b),
  (D.map f).toOrderHom (Fin.last (D.obj a).len) = Fin.last (D.obj b).len)
variable (r : ∀ b : B, (NecklaceCode.single (D.obj b).len).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app (base.obj b)) j j le_rfl).toSSet)
private abbrev native (b : B) :=
  r b ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app (base.obj b)) j
variable (hr : ∀ {a b : B} (f : a ⟶ b),
  (NecklaceCode.singleIso (D.obj a).len).inv ≫ native F j base D r a ≫
    ((codes L).map (base.map f)).map =
  std.map (D.map f) ≫ (NecklaceCode.singleIso (D.obj b).len).inv ≫
    native F j base D r b)

/-- Original old coefficient degrees of the overlap bead. -/
abbrev oldDegrees := JTJointBeadEndpointDiagram.oldDegrees (L := L) base

/-- The full timed support degrees of the overlap bead. -/
abbrev degrees := JTJointBeadOverlapDiagram.degrees F j base D r hr

/-- The naturally varying inclusion of the full support face. -/
abbrev incl := JTJointBeadEndpointDiagram.incl F j base D r hr

/-- Full simplicial spaces of front and back edge choices on one common clock. -/
abbrev spaces := JTTwoEndpointChoiceCover.spaces W (degrees F j base D r hr)
  (oldDegrees (L := L) base) (incl F j base D r hr)
  (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
  (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
  (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)

/-- All higher choices over the original bead diagram. -/
abbrev Cover := JTTwoEndpointChoiceCover.Cover W (degrees F j base D r hr)
  (oldDegrees (L := L) base) (incl F j base D r hr)
  (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
  (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
  (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)

/-- Forget the full higher endpoint choice while retaining the old chart. -/
abbrev projection : Cover F j base D h₀ h₁ r hr ⥤ B :=
  JTTwoEndpointChoiceCover.projection W (degrees F j base D r hr)
    (oldDegrees (L := L) base) (incl F j base D r hr)
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)

/-- The shared higher-choice simplex degree. -/
abbrev choiceTime : Cover F j base D h₀ h₁ r hr ⥤ SimplexCategory :=
  JTTwoEndpointChoiceCover.choiceTime W (degrees F j base D r hr)
    (oldDegrees (L := L) base) (incl F j base D r hr)
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)

/-- Old coefficient degrees after the weak full-choice cover. -/
abbrev coefficient : Cover F j base D h₀ h₁ r hr ⥤ SimplexCategory :=
  projection F j base D h₀ h₁ r hr ⋙ oldDegrees (L := L) base

/-- The common coefficient-choice-time prisms of the full bead choices. -/
abbrev prisms := JTTwoEndpointChoicePrism.prisms W (degrees F j base D r hr)
  (oldDegrees (L := L) base) (incl F j base D r hr)
  (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
  (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
  (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)

/-- Natural full front edge, stationary on the full timed support. -/
abbrev front := JTTwoEndpointChoicePrism.front W (degrees F j base D r hr)
  (oldDegrees (L := L) base) (incl F j base D r hr)
  (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
  (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
  (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)

/-- Natural full back edge on the same coefficient-choice-time prisms. -/
abbrev back := JTTwoEndpointChoicePrism.back W (degrees F j base D r hr)
  (oldDegrees (L := L) base) (incl F j base D r hr)
  (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
  (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
  (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
  (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)

/-- The full higher endpoint choices form a nerve weak cover of the bead diagram. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j base D h₀ h₁ r hr)) :=
  JTTwoEndpointChoiceCover.projection_weak W (degrees F j base D r hr)
    (oldDegrees (L := L) base) (incl F j base D r hr)
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)
    hW (JTJointBeadEndpointDiagram.incl_mono F j base D r hr)

end
end DaggerModels.PartII.JTJointBeadFullSupportChoices
