import DaggerModelsPartII.JTOrdinalInverseFaceDiagram
import DaggerModelsPartII.JTJointBeadNormalizationDiagram
import DaggerModelsPartII.JTSupportedNormalizedLabel

/-! Natural full inverse-image support of the normalized joint-bead chains. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointBeadNormalizationSupport

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
private abbrev oldSupport := charts F j base D h₀ h₁ r hr ⋙
  JTJointBeadFullSupportChoices.degrees F j base D r hr
private abbrev oldDegree := charts F j base D h₀ h₁ r hr ⋙
  JTJointBeadFullSupportChoices.oldDegrees (L := L) base
private abbrev newDegree := JTJointBeadNormalizationDiagram.ordinals F j base D h₀ h₁ r hr

/-- The original full timed support face, pulled to every normalized chain. -/
def oldIncl : oldSupport F j base D h₀ h₁ r hr ⟶
    oldDegree F j base D h₀ h₁ r hr :=
  Functor.whiskerLeft (charts F j base D h₀ h₁ r hr)
    (JTJointBeadEndpointDiagram.incl F j base D r hr)

private theorem oldIncl_mono (p : I F j base D h₀ h₁ r hr) :
    Mono ((oldIncl F j base D h₀ h₁ r hr).app p) :=
  JTJointBeadEndpointDiagram.incl_mono F j base D r hr
    ((charts F j base D h₀ h₁ r hr).obj p)

private abbrev α := JTJointBeadNormalizationDiagram.toOriginal F j base D h₀ h₁ r hr

/-- The full inverse image of the old used face under the chain's surjective
coefficient projection. -/
abbrev support : I F j base D h₀ h₁ r hr ⥤ SimplexCategory :=
  JTOrdinalInverseFaceDiagram.supportDiagram
    (oldSupport F j base D h₀ h₁ r hr)
    (oldDegree F j base D h₀ h₁ r hr)
    (newDegree F j base D h₀ h₁ r hr)
    (oldIncl F j base D h₀ h₁ r hr)
    (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr)

/-- Natural inclusion in the original chain degree. -/
abbrev incl : support F j base D h₀ h₁ r hr ⟶
    newDegree F j base D h₀ h₁ r hr :=
  JTOrdinalInverseFaceDiagram.inclNat _ _ _
    (oldIncl F j base D h₀ h₁ r hr) (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr)

/-- Natural coordinate in the old full timed support. -/
abbrev toOldSupport : support F j base D h₀ h₁ r hr ⟶
    oldSupport F j base D h₀ h₁ r hr :=
  JTOrdinalInverseFaceDiagram.toFaceNat _ _ _
    (oldIncl F j base D h₀ h₁ r hr) (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr)

/-- The natural full-inverse-image square is strict. -/
theorem natural_square :
    toOldSupport F j base D h₀ h₁ r hr ≫ oldIncl F j base D h₀ h₁ r hr =
      incl F j base D h₀ h₁ r hr ≫ α F j base D h₀ h₁ r hr :=
  JTOrdinalInverseFaceDiagram.natural_square _ _ _
    (oldIncl F j base D h₀ h₁ r hr) (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr)

/-- Each full inverse-image inclusion is monic. -/
theorem incl_mono (p : I F j base D h₀ h₁ r hr) :
    Mono ((incl F j base D h₀ h₁ r hr).app p) :=
  JTOrdinalInverseFaceDiagram.incl_mono _ _ _
    (oldIncl F j base D h₀ h₁ r hr) (α F j base D h₀ h₁ r hr)
    (oldIncl_mono F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationDiagram.toOriginal_surjective F j base D h₀ h₁ r hr) p

private theorem square_at (p : I F j base D h₀ h₁ r hr) :
    (incl F j base D h₀ h₁ r hr).app p ≫
        (α F j base D h₀ h₁ r hr).app p =
      (toOldSupport F j base D h₀ h₁ r hr).app p ≫
        (oldIncl F j base D h₀ h₁ r hr).app p :=
  (congrArg (fun η : support F j base D h₀ h₁ r hr ⟶
    oldDegree F j base D h₀ h₁ r hr ↦ η.app p)
      (natural_square F j base D h₀ h₁ r hr)).symm

/-- The old native bead is constant after restricting the complete chain
coefficient to its natural full inverse-image support. -/
theorem middle_onSupport (p : I F j base D h₀ h₁ r hr) :
    std.map ((incl F j base D h₀ h₁ r hr).app p) ≫
      JTJointBeadNormalizationDiagram.oldMiddle F j base D h₀ h₁ r hr p =
    JTConstantOrderedLabel.constantCoefficient W
      (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
      (single (D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len)
      ((support F j base D h₀ h₁ r hr).obj p) := by
  rw [JTJointBeadNormalizationDiagram.oldMiddle_eq]
  rw [← Category.assoc, ← std.map_comp, square_at]
  rw [std.map_comp, Category.assoc]
  change std.map ((toOldSupport F j base D h₀ h₁ r hr).app p) ≫
    (std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F
      (base.obj ((charts F j base D h₀ h₁ r hr).obj p))
      (D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len
      (native F j base D r ((charts F j base D h₀ h₁ r hr).obj p))) ≫
      JTJointBeadSupportedNormalization.coefficient F
        (base.obj ((charts F j base D h₀ h₁ r hr).obj p))
        (D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len j
        (r ((charts F j base D h₀ h₁ r hr).obj p))) = _
  rw [JTJointBeadSupportedNormalization.coefficient_onSupport]
  exact (JTConstantOrderedLabel.constantCoefficient_ordinal W
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (single (D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len)
    ((toOldSupport F j base D h₀ h₁ r hr).app p)).symm

private theorem front_row_onSupport (p : I F j base D h₀ h₁ r hr) :
    std.map ((incl F j base D h₀ h₁ r hr).app p) ≫
      (JTJointBeadNormalizationDiagram.front F j base D h₀ h₁ r hr).app p =
    JTJointEndpointRelativeLift.identityOnFace W
      (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  let c := (JTJointBeadNormalizationDiagram.chainBase F j base D h₀ h₁ r hr).obj p
  let v := (incl F j base D h₀ h₁ r hr).app p
  let q := (toOldSupport F j base D h₀ h₁ r hr).app p
  let a := (α F j base D h₀ h₁ r hr).app p
  let b := (JTJointBeadNormalizationDiagram.toChoice F j base D h₀ h₁ r hr).app p
  have hs : v ≫ a = q ≫
      (JTJointBeadFullSupportChoices.incl F j base D r hr).app
        ((JTJointBeadFullSupportChoices.projection F j base D h₀ h₁ r hr).obj c) :=
    square_at F j base D h₀ h₁ r hr p
  change std.map v ≫ lift (std.map a) (std.map b) ≫
    (JTJointBeadFullSupportChoices.front F j base D h₀ h₁ r hr).app c = _
  exact JTTwoEndpointChoicePrism.front_chain_face W
    (JTJointBeadFullSupportChoices.degrees F j base D r hr)
    (JTJointBeadFullSupportChoices.oldDegrees (L := L) base)
    (JTJointBeadFullSupportChoices.incl F j base D r hr)
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)
    c a b v q hs

private theorem back_row_onSupport (p : I F j base D h₀ h₁ r hr) :
    std.map ((incl F j base D h₀ h₁ r hr).app p) ≫
      (JTJointBeadNormalizationDiagram.back F j base D h₀ h₁ r hr).app p =
    JTJointEndpointRelativeLift.identityOnFace W
      (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  let c := (JTJointBeadNormalizationDiagram.chainBase F j base D h₀ h₁ r hr).obj p
  let v := (incl F j base D h₀ h₁ r hr).app p
  let q := (toOldSupport F j base D h₀ h₁ r hr).app p
  let a := (α F j base D h₀ h₁ r hr).app p
  let b := (JTJointBeadNormalizationDiagram.toChoice F j base D h₀ h₁ r hr).app p
  have hs : v ≫ a = q ≫
      (JTJointBeadFullSupportChoices.incl F j base D r hr).app
        ((JTJointBeadFullSupportChoices.projection F j base D h₀ h₁ r hr).obj c) :=
    square_at F j base D h₀ h₁ r hr p
  change std.map v ≫ lift (std.map a) (std.map b) ≫
    (JTJointBeadFullSupportChoices.back F j base D h₀ h₁ r hr).app c = _
  exact JTTwoEndpointChoicePrism.back_chain_face W
    (JTJointBeadFullSupportChoices.degrees F j base D r hr)
    (JTJointBeadFullSupportChoices.oldDegrees (L := L) base)
    (JTJointBeadFullSupportChoices.incl F j base D r hr)
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr)
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)
    c a b v q hs

/-- The front native edge is constant on the natural inverse-image support. -/
theorem front_onSupport (p : I F j base D h₀ h₁ r hr) :
    std.map ((incl F j base D h₀ h₁ r hr).app p) ≫
      (JTJointBeadNormalizationDiagram.data F j base D h₀ h₁ r hr p).left =
    JTConstantOrderedLabel.constantCoefficient W
      (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
      (single 1) ((support F j base D h₀ h₁ r hr).obj p) := by
  apply JTWhiskerEdgeCoefficient.onFace W
    ((incl F j base D h₀ h₁ r hr).app p)
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    ((JTJointBeadNormalizationDiagram.front F j base D h₀ h₁ r hr).app p)
  exact front_row_onSupport F j base D h₀ h₁ r hr p

/-- The back native edge is constant on the same inverse-image support. -/
theorem back_onSupport (p : I F j base D h₀ h₁ r hr) :
    std.map ((incl F j base D h₀ h₁ r hr).app p) ≫
      (JTJointBeadNormalizationDiagram.data F j base D h₀ h₁ r hr p).right =
    JTConstantOrderedLabel.constantCoefficient W
      (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
      (single 1) ((support F j base D h₀ h₁ r hr).obj p) := by
  apply JTWhiskerEdgeCoefficient.onFace W
    ((incl F j base D h₀ h₁ r hr).app p)
    (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    ((JTJointBeadNormalizationDiagram.back F j base D h₀ h₁ r hr).app p)
  exact back_row_onSupport F j base D h₀ h₁ r hr p

/-- The complete normalized triple, in its unchanged chain degree, is the
literal joint label on the natural full inverse-image support. -/
theorem coefficient_onSupport (p : I F j base D h₀ h₁ r hr) :
    std.map ((incl F j base D h₀ h₁ r hr).app p) ≫
      JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients
          (JTJointBeadNormalizationDiagram.data F j base D h₀ h₁ r hr p)) =
    JTConstantOrderedLabel.constantCoefficient W
      (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
      (wedge (single 1)
        (wedge (single (D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len)
          (single 1)))
      ((support F j base D h₀ h₁ r hr).obj p) := by
  let C := JTJointBeadNormalizationDiagram.data F j base D h₀ h₁ r hr p
  let N : JTSupportedNormalizedLabel.Data W
      (single (D.obj ((charts F j base D h₀ h₁ r hr).obj p)).len)
      ((newDegree F j base D h₀ h₁ r hr).obj p)
      (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) :=
    { middle := C.middle
      front := C.left
      back := C.right
      front_join := C.left_join
      back_join := C.right_join
      first := C.first
      last := C.last }
  change std.map ((incl F j base D h₀ h₁ r hr).app p) ≫
    JTComposedPrismLabels.coefficient (JTSupportedNormalizedLabel.coefficients N) = _
  exact JTSupportedNormalizedLabel.coefficient_onFace N
    ((incl F j base D h₀ h₁ r hr).app p)
    (middle_onSupport F j base D h₀ h₁ r hr p)
    (front_onSupport F j base D h₀ h₁ r hr p)
    (back_onSupport F j base D h₀ h₁ r hr p)

end
end DaggerModels.PartII.JTJointBeadNormalizationSupport
