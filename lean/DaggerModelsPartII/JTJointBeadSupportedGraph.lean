import DaggerModelsPartII.JTJointBeadNormalizationSupport
import DaggerModelsPartII.JTOrdinalInverseFaceParameterDiagram
import DaggerModelsPartII.JTPrismChainGraphCover
import DaggerModelsPartII.JTNativeEndpointPadding
import DaggerModelsPartII.JTSupportedPathGraphData

/-! The complete native and timed graph of an actually normalized joint bead. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointBeadSupportedGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
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
variable (r : ∀ b : B, (single (D.obj b).len).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app (base.obj b)) j j le_rfl).toSSet)
private abbrev native (b : B) :=
  r b ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app (base.obj b)) j
variable (hr : ∀ {a b : B} (f : a ⟶ b),
  (singleIso (D.obj a).len).inv ≫ native F j base D r a ≫
    ((codes L).map (base.map f)).map =
  std.map (D.map f) ≫ (singleIso (D.obj b).len).inv ≫ native F j base D r b)

private abbrev I := JTJointBeadNormalizationDiagram.Index F j base D h₀ h₁ r hr
private abbrev charts := JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr
private abbrev beadCodes := charts F j base D h₀ h₁ r hr ⋙
  JTJointBeadOverlapDiagram.natives D h₀ h₁
private abbrev paddedCodes := beadCodes F j base D h₀ h₁ r hr ⋙ JTNativeEndpointPadding.pad
private abbrev oldTime := charts F j base D h₀ h₁ r hr ⋙ base ⋙ time
private abbrev oldDegree := charts F j base D h₀ h₁ r hr ⋙
  JTJointBeadOverlapDiagram.oldDegrees L base
private abbrev oldSupport := charts F j base D h₀ h₁ r hr ⋙
  JTJointBeadOverlapDiagram.degrees F j base D r hr
private abbrev newDegree := JTJointBeadNormalizationDiagram.ordinals F j base D h₀ h₁ r hr
private abbrev α := JTJointBeadNormalizationDiagram.toOriginal F j base D h₀ h₁ r hr

/-- The normalized three-piece labels have exactly the padded single-bead native code. -/
theorem labels_codes :
    codes (JTJointBeadNormalizationDiagram.labels F j base D h₀ h₁ r hr) =
      paddedCodes F j base D h₀ h₁ r hr := rfl

/-- Complete padded native and original time, before any coefficient lift. -/
abbrev X : I F j base D h₀ h₁ r hr ⥤ SSet.{0} :=
  (((paddedCodes F j base D h₀ h₁ r hr) ⋙ NecklaceCode.simplicialFunctor).prod'
    ((oldTime F j base D h₀ h₁ r hr) ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}

private abbrev beadX : I F j base D h₀ h₁ r hr ⥤ SSet.{0} :=
  (((beadCodes F j base D h₀ h₁ r hr) ⋙ NecklaceCode.simplicialFunctor).prod'
    ((oldTime F j base D h₀ h₁ r hr) ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}

/-- Collapse the two padded native edges, keeping the original time coordinate. -/
def collapseX : X F j base D h₀ h₁ r hr ⟶ beadX F j base D h₀ h₁ r hr :=
  Functor.whiskerRight
    (NatTrans.prod'
      (Functor.whiskerRight
        (Functor.whiskerLeft (beadCodes F j base D h₀ h₁ r hr)
          JTNativeEndpointPadding.collapse) NecklaceCode.simplicialFunctor)
      (𝟙 ((oldTime F j base D h₀ h₁ r hr) ⋙ J)))
    (MonoidalCategory.tensor SSet.{0})

/-- The original old used-support parameter on the unpadded native graph. -/
def beadParameter : beadX F j base D h₀ h₁ r hr ⟶
    oldSupport F j base D h₀ h₁ r hr ⋙ J where
  app p := JTJointBeadOverlapDiagram.nativeParameter F j base D h₀ h₁ r hr
    ((charts F j base D h₀ h₁ r hr).obj p)
  naturality _ _ q :=
    (JTJointBeadOverlapDiagram.family F j base D h₀ h₁ r hr).parameter_map
      ((charts F j base D h₀ h₁ r hr).map q)

/-- The complete padded graph parameter, already confined to the old full timed face. -/
def oldSupportParameter : X F j base D h₀ h₁ r hr ⟶
    oldSupport F j base D h₀ h₁ r hr ⋙ J :=
  collapseX F j base D h₀ h₁ r hr ≫ beadParameter F j base D h₀ h₁ r hr

/-- Its original full old-degree parameter, before chain lifting. -/
def oldParameter : X F j base D h₀ h₁ r hr ⟶
    oldDegree F j base D h₀ h₁ r hr ⋙ J :=
  oldSupportParameter F j base D h₀ h₁ r hr ≫
    Functor.whiskerRight (JTJointBeadNormalizationSupport.oldIncl
      F j base D h₀ h₁ r hr) J

/-- The old-degree graph parameter is the original complete timed bead
parameter after collapsing the two padded native edges. -/
theorem oldParameter_original (p : I F j base D h₀ h₁ r hr) :
    (oldParameter F j base D h₀ h₁ r hr).app p =
      (((JTNativeEndpointPadding.collapse.app
          ((beadCodes F j base D h₀ h₁ r hr).obj p)).map ⊗ₘ 𝟙 _) ≫
        ((singleIso ((D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len)).hom
          ⊗ₘ 𝟙 _)) ≫
        (JTJointBeadOverlapDiagram.originalParameter F j base D r hr).app
          ((charts F j base D h₀ h₁ r hr).obj p) := by
  have h := congrArg (fun η ↦ η.app ((charts F j base D h₀ h₁ r hr).obj p))
    (JTFullPrismSupportedDiagram.parameter_fac
      (JTJointBeadOverlapDiagram.originalParameter F j base D r hr))
  change (JTJointBeadOverlapDiagram.parameter F j base D r hr).app _ ≫
      J.map ((JTJointBeadEndpointDiagram.incl F j base D r hr).app _) =
    (JTJointBeadOverlapDiagram.originalParameter F j base D r hr).app _ at h
  change (((JTNativeEndpointPadding.collapse.app
      ((beadCodes F j base D h₀ h₁ r hr).obj p)).map ⊗ₘ 𝟙 _) ≫
      ((singleIso ((D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len)).hom
        ⊗ₘ 𝟙 _)) ≫
      (JTJointBeadOverlapDiagram.parameter F j base D r hr).app _ ≫
      J.map ((JTJointBeadEndpointDiagram.incl F j base D r hr).app _) = _
  rw [Category.assoc, h]
  simp only [Category.assoc]

/-- All coefficient lifts to the actual surjective normalization chain. -/
abbrev graph : I F j base D h₀ h₁ r hr ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (X F j base D h₀ h₁ r hr)
    (oldParameter F j base D h₀ h₁ r hr) (α F j base D h₀ h₁ r hr)

/-- Project to the complete padded native and original-time graph. -/
abbrev projection : graph F j base D h₀ h₁ r hr ⟶ X F j base D h₀ h₁ r hr :=
  JTPrismChainGraphCover.projection (X F j base D h₀ h₁ r hr)
    (oldParameter F j base D h₀ h₁ r hr) (α F j base D h₀ h₁ r hr)

/-- The lifted parameter retains every normalization-chain ordinal coordinate. -/
abbrev parameter : graph F j base D h₀ h₁ r hr ⟶
    newDegree F j base D h₀ h₁ r hr ⋙ J :=
  JTPrismChainGraphCover.parameter (X F j base D h₀ h₁ r hr)
    (oldParameter F j base D h₀ h₁ r hr) (α F j base D h₀ h₁ r hr)

/-- Each graph projection is an objectwise trivial fibration. -/
theorem projection_trivialFibration (p : I F j base D h₀ h₁ r hr) :
    trivialFibrations SSet.{0} ((projection F j base D h₀ h₁ r hr).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration
    (X F j base D h₀ h₁ r hr) (oldParameter F j base D h₀ h₁ r hr)
    (α F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr) p

/-- The lifted parameter has the exact original old-degree projection. -/
theorem parameter_projection :
    parameter F j base D h₀ h₁ r hr ≫
      Functor.whiskerRight (α F j base D h₀ h₁ r hr) J =
    projection F j base D h₀ h₁ r hr ≫ oldParameter F j base D h₀ h₁ r hr :=
  JTPrismChainGraphCover.parameter_projection
    (X F j base D h₀ h₁ r hr) (oldParameter F j base D h₀ h₁ r hr)
    (α F j base D h₀ h₁ r hr)

/-- The unchanged full timed parameter on the old bead's actual used face. -/
def oldSupportOnGraph : graph F j base D h₀ h₁ r hr ⟶
    oldSupport F j base D h₀ h₁ r hr ⋙ J :=
  projection F j base D h₀ h₁ r hr ≫ oldSupportParameter F j base D h₀ h₁ r hr

private theorem oldIncl_mono (p : I F j base D h₀ h₁ r hr) :
    Mono ((JTJointBeadNormalizationSupport.oldIncl F j base D h₀ h₁ r hr).app p) :=
  JTJointBeadEndpointDiagram.incl_mono F j base D r hr
    ((charts F j base D h₀ h₁ r hr).obj p)

private theorem oldSquare :
    parameter F j base D h₀ h₁ r hr ≫
      Functor.whiskerRight (α F j base D h₀ h₁ r hr) J =
    oldSupportOnGraph F j base D h₀ h₁ r hr ≫
      Functor.whiskerRight
        (JTJointBeadNormalizationSupport.oldIncl F j base D h₀ h₁ r hr) J := by
  rw [parameter_projection]
  rfl

/-- Full graph parameter on the new inverse-image support, natural in all arrows. -/
def supportParameter : graph F j base D h₀ h₁ r hr ⟶
    JTJointBeadNormalizationSupport.support F j base D h₀ h₁ r hr ⋙ J :=
  JTOrdinalInverseFaceParameterDiagram.factor
    (oldSupport F j base D h₀ h₁ r hr)
    (oldDegree F j base D h₀ h₁ r hr)
    (newDegree F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.oldIncl F j base D h₀ h₁ r hr)
    (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr)
    (graph F j base D h₀ h₁ r hr)
    (parameter F j base D h₀ h₁ r hr)
    (oldSupportOnGraph F j base D h₀ h₁ r hr)
    (oldSquare F j base D h₀ h₁ r hr)

/-- The new supported parameter recovers the exact chain parameter. -/
theorem support_fac :
    supportParameter F j base D h₀ h₁ r hr ≫
      Functor.whiskerRight
        (JTJointBeadNormalizationSupport.incl F j base D h₀ h₁ r hr) J =
    parameter F j base D h₀ h₁ r hr :=
  JTOrdinalInverseFaceParameterDiagram.factor_incl
    (oldSupport F j base D h₀ h₁ r hr)
    (oldDegree F j base D h₀ h₁ r hr)
    (newDegree F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.oldIncl F j base D h₀ h₁ r hr)
    (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr)
    (graph F j base D h₀ h₁ r hr)
    (parameter F j base D h₀ h₁ r hr)
    (oldSupportOnGraph F j base D h₀ h₁ r hr)
    (oldSquare F j base D h₀ h₁ r hr)

/-- The new support coordinate projects to the actual old full timed support. -/
theorem support_toOld :
    supportParameter F j base D h₀ h₁ r hr ≫
      Functor.whiskerRight
        (JTJointBeadNormalizationSupport.toOldSupport F j base D h₀ h₁ r hr) J =
    oldSupportOnGraph F j base D h₀ h₁ r hr :=
  JTOrdinalInverseFaceParameterDiagram.factor_toOld
    (oldSupport F j base D h₀ h₁ r hr)
    (oldDegree F j base D h₀ h₁ r hr)
    (newDegree F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.oldIncl F j base D h₀ h₁ r hr)
    (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr)
    (graph F j base D h₀ h₁ r hr)
    (parameter F j base D h₀ h₁ r hr)
    (oldSupportOnGraph F j base D h₀ h₁ r hr)
    (oldSquare F j base D h₀ h₁ r hr)

/-- The actual normalized bead supplies the generic supported path graph data. -/
def data : JTSupportedPathGraphData.GraphData W (jointCoefficient (Q := Q) j)
    (JTJointBeadNormalizationDiagram.labels F j base D h₀ h₁ r hr)
    (oldTime F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.support F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.incl F j base D h₀ h₁ r hr) where
  domain := graph F j base D h₀ h₁ r hr
  projection := projection F j base D h₀ h₁ r hr
  parameter := parameter F j base D h₀ h₁ r hr
  supportParameter := supportParameter F j base D h₀ h₁ r hr
  support_fac := support_fac F j base D h₀ h₁ r hr

end
end DaggerModels.PartII.JTJointBeadSupportedGraph
