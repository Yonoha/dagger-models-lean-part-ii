import DaggerModelsPartII.JTEndpointSimplexSlice
import DaggerModelsPartII.JTSupportedChoiceBeadEvaluation
import DaggerModelsPartII.JTGraphInterpolatedSourceComparison
import DaggerModelsPartII.SynchronizedSimplicialParameters
import NativeOverNerveWeakContractibility

/-! All endpoint-preserving restrictions of the joint choices over one raw bead. -/

set_option autoImplicit false
set_option maxHeartbeats 180000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointHorizontalChoice

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTRowGraphCommonCenter JTEndpointSimplexSlice JTNecklaceEndpointCylinder
open NecklaceCylinderJointDiagram (cylinderUnder)
open MixedGraphCylinderTraversal (code collapseOuter)
open JTGraphFactoredPresentation (TargetComma)
open BoundaryNecklaceComma (necklaceUnder fiberDiagram)

noncomputable section

/-- A padded source map commutes with the native collapse and its middle operator. -/
theorem native_after_source {e d : ℕ} (f : single e ⟶ single d) (k : SimplexCategory) :
    JTGraphInterpolatedSourceComparison.sourceMap (JTMixedGraphHorizontalTraversal.padded f) k ≫
        JTHigherMixedGraphTargetLift.toNativeTarget d k =
      JTHigherMixedGraphTargetLift.toNativeTarget e k ≫ necklaceUnder.map f := by
  apply Under.UnderMorphism.ext
  change nativeMap (JTMixedGraphHorizontalTraversal.padded f) k ≫
      (NecklaceCylinderAugmentation.augmentation (code d) k ≫ (collapseOuter d).map) =
    (NecklaceCylinderAugmentation.augmentation (code e) k ≫ (collapseOuter e).map) ≫ f.map
  rw [← Category.assoc, NecklaceCylinderAugmentation.augmentation_native_natural,
    Category.assoc, Category.assoc]
  exact congrArg (fun u : code e ⟶ single d ↦
    NecklaceCylinderAugmentation.augmentation (code e) k ≫ u.map)
    (JTMixedGraphHorizontalTraversal.collapse_natural f)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy

/-- A horizontal operator into the fixed simplex and a joint choice on that simplex. -/
abbrev Index := Slice d × JointChoiceIndex hx hy

private abbrev forgetHorizontal : Index hx hy ⥤ JointChoiceIndex hx hy :=
  CategoryTheory.Prod.snd _ _

private abbrev time := choiceTime q hx hy

/-- Use the actual reduced cylinder of the operator's source with the inherited time. -/
abbrev cylinders : Index hx hy ⥤ Under JTXiEndpointCollapse.boundary :=
  ((paddedSource d).prod (time hx hy)) ⋙ cylinderUnder

/-- The original padded operator induces a natural map of all reduced cylinders. -/
def toParentCylinder : cylinders hx hy ⟶ forgetHorizontal hx hy ⋙ choiceCylinders hx hy where
  app A := JTGraphInterpolatedSourceComparison.sourceMap
    ((paddedToTarget d).app A.1) ((time hx hy).obj A.2)
  naturality {A B} f := by
    apply Under.UnderMorphism.ext
    change
      (nativeMap ((paddedSource d).map f.1) ((time hx hy).obj A.2) ≫
        (value ((paddedSource d).obj B.1)).map ((time hx hy).map f.2)) ≫
          nativeMap ((paddedToTarget d).app B.1) ((time hx hy).obj B.2) =
      nativeMap ((paddedToTarget d).app A.1) ((time hx hy).obj A.2) ≫
        (value (code d)).map ((time hx hy).map f.2)
    rw [Category.assoc, nativeMap_parameter_natural, ← Category.assoc, ← nativeMap_comp]
    have h := (paddedToTarget d).naturality f.1
    change (paddedSource d).map f.1 ≫ (paddedToTarget d).app B.1 =
      (paddedToTarget d).app A.1 ≫ 𝟙 _ at h
    rw [h, Category.comp_id]
    rfl

/-- Retain every endpoint-preserving internal necklace and its morphisms. -/
abbrev Resolution := BoundaryNecklaceComma.Presentation (cylinders hx hy)

/-- Compose each internal traversal with its actual map into the parent cylinder. -/
abbrev toParent : Resolution hx hy ⥤ ChoiceResolution hx hy :=
  JTBoundaryNecklacePresentationCone.mapPresentation (choiceCylinders hx hy)
    (cylinders hx hy) (forgetHorizontal hx hy) (toParentCylinder hx hy)

/-- Evaluate the restricted cylinders at the same original fixed target. -/
def evaluation : Resolution hx hy ⥤ TargetComma (Q hx hy) :=
  toParent hx hy ⋙ choiceEvaluation hx hy

/-- The comparison to the parent collapses the padded source, followed by its original horizontal map. -/
theorem toParentCylinder_native (A : Index hx hy) :
    (toParentCylinder hx hy).app A ≫
        JTHigherMixedGraphTargetLift.toNativeTarget d ((time hx hy).obj A.2) =
      JTHigherMixedGraphTargetLift.toNativeTarget A.1.left.obj.len ((time hx hy).obj A.2) ≫
        necklaceUnder.map (bead.map A.1.hom) :=
  native_after_source (e := A.1.left.obj.len) (d := d)
    (bead.map A.1.hom) ((time hx hy).obj A.2)

private theorem resolution_projection_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget (fiberDiagram (cylinders hx hy)))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun A ↦
    JTHomotopyTargetComma.fiber_point_GW_at ((paddedSource d).obj A.1) ((time hx hy).obj A.2))

/-- Taking all endpoint-preserving horizontal operators preserves weak contractibility. -/
theorem resolution_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (Resolution hx hy))) := by
  let P := Grothendieck.forget (fiberDiagram (cylinders hx hy))
  let p := pointMap (nerve (Index hx hy))
  letI : WeakEquivalence (nerveMap P) := resolution_projection_weak hx hy
  letI : WeakEquivalence p := (weakEquivalence_iff_GW _).mpr
    (SynchronizedSimplicialParameters.bases_point_GW
      (DaggerNativeOverNerveWeakContractibility.point_GW (simplex d))
      (jointChoiceIndex_point_GW hx hy hW))
  rw [← pointIsTerminal.hom_ext (nerveMap P ≫ p) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerModels.PartII.JTEndpointHorizontalChoice
