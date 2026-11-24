import DaggerModelsPartII.JTIncidentBeadSupportTransport
import DaggerModelsPartII.JTIncidentBeadSupportWeak
import DaggerModelsPartII.JTSubcomplexRelativeChoiceDiagram
import DaggerModelsPartII.JTActualJointChoiceCover

/-!
# Full relative choices on the actual incident support union

Every ending and starting edge is stationary on the genuine union of incident
full timed bead faces. The source, coefficient operators and vertex row are
those of the original exactly marked family. The complete paired choice cover
is weak over that exactly marked source; no weak marked projection is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory
open DaggerSSetGluing DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTIncidentBeadChoiceDiagram

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTExactlyMarkedSourceDiagram (Index degrees endpointRows)
open JTIncidentBeadSupportTransport (diagram inclusion vertexToSupport vertexToSupport_fac)
open JTJointEndpointLiftSpaceRestriction (precompSquare precompSquare_ι)
open GrothendieckTotalElements (totalDiagram)
open DaggerOriginalProductGadget (pointMap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private def tensorNat {C : Type} [SmallCategory C]
    {P P' R R' : C ⥤ SSet.{0}} (α : P ⟶ P') (β : R ⟶ R') :
    Functor.diag C ⋙ P.prod R ⋙ MonoidalCategory.tensor SSet.{0} ⟶
      Functor.diag C ⋙ P'.prod R' ⋙ MonoidalCategory.tensor SSet.{0} where
  app p := α.app p ⊗ₘ β.app p
  naturality p q f := by
    change (P.map f ⊗ₘ R.map f) ≫ (α.app q ⊗ₘ β.app q) =
      (α.app p ⊗ₘ β.app p) ≫ (P'.map f ⊗ₘ R'.map f)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun a b ↦ a ⊗ₘ b) (α.naturality f) (β.naturality f)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- The actual full ending-edge space, stationary on every incident timed bead face. -/
abbrev endingSpaces : (Index F j)ᵒᵖ ⥤ SSet.{0} :=
  JTSubcomplexRelativeChoiceDiagram.leftChoices W (diagram F j) (degrees F j)
    (inclusion F j) (endpointRows F j) (z j) (JTIncidentBeadSupportData.row_on_support F j)

/-- The corresponding full starting-edge space on the very same original coefficient. -/
abbrev startingSpaces : (Index F j)ᵒᵖ ⥤ SSet.{0} :=
  JTSubcomplexRelativeChoiceDiagram.rightChoices W (diagram F j) (degrees F j)
    (inclusion F j) (endpointRows F j) (z j) (JTIncidentBeadSupportData.row_on_support F j)

/-- Both orientations share all higher simplices and the same choice clock. -/
abbrev spaces : (Index F j)ᵒᵖ ⥤ SSet.{0} :=
  JTSubcomplexRelativeChoiceDiagram.pairChoices W (diagram F j) (degrees F j)
    (inclusion F j) (endpointRows F j) (z j) (JTIncidentBeadSupportData.row_on_support F j)

private abbrev leftSquare (p : Index F j) :=
  JTJointSubcomplexRelativeLift.square W ((inclusion F j).app p)
    ((endpointRows F j).app p) (z j) (JTIncidentBeadSupportData.row_on_support F j p)

private abbrev rightSquare (p : Index F j) :=
  JTJointSubcomplexRelativeLift.reverseSquare W ((inclusion F j).app p)
    ((endpointRows F j).app p) (z j) (JTIncidentBeadSupportData.row_on_support F j p)

private abbrev oldLeftSquare (p : Index F j) :=
  JTJointEndpointRelativeLift.square W ((JTExactlyMarkedSourceDiagram.incl F j).app p)
    ((endpointRows F j).app p) (z j) (JTExactlyMarkedSourceDiagram.supported_endpoint F j p)

private abbrev oldRightSquare (p : Index F j) :=
  JTJointEndpointRelativeLift.reverseSquare W ((JTExactlyMarkedSourceDiagram.incl F j).app p)
    ((endpointRows F j).app p) (z j) (JTExactlyMarkedSourceDiagram.supported_endpoint F j p)

private theorem support_face (p : Index F j) :
    (vertexToSupport F j).app p ≫ (inclusion F j).app p =
      std.map ((JTExactlyMarkedSourceDiagram.incl F j).app p) ≫ 𝟙 _ := by
  rw [Category.comp_id]
  exact NatTrans.congr_app (vertexToSupport_fac F j) p

private theorem support_identity (p : Index F j) :
    (vertexToSupport F j).app p ≫ JTJointSubcomplexRelativeLift.identityOnU W (z j) =
      JTJointEndpointRelativeLift.identityOnFace W (z j)
        (l := (JTExactlyMarkedSourceDiagram.supports F j).obj p) := by
  change (vertexToSupport F j).app p ≫
      (term ((diagram F j).obj p) ≫ JTProjectiveOrderedFiberComparison.vertexPoint W (z j) ≫
        JTEndpointNormalizationLifts.identityFamily W) =
    term _ ≫ JTProjectiveOrderedFiberComparison.vertexPoint W (z j) ≫
      JTEndpointNormalizationLifts.identityFamily W
  rw [← Category.assoc]
  congr 1

private def endingRestriction (p : Index F j) :
    (endingSpaces F j).obj (op p) ⟶ (JTActualJointChoiceCover.endingSpaces F j).obj (op p) :=
  precompSquare (leftSquare F j p) (oldLeftSquare F j p)
    ((vertexToSupport F j).app p) (𝟙 _) (support_face F j p)
    (support_identity F j p) (Category.id_comp _)

private def startingRestriction (p : Index F j) :
    (startingSpaces F j).obj (op p) ⟶
      (JTActualJointChoiceCover.startingSpaces F j).obj (op p) :=
  precompSquare (rightSquare F j p) (oldRightSquare F j p)
    ((vertexToSupport F j).app p) (𝟙 _) (support_face F j p)
    (support_identity F j p) (Category.id_comp _)

private theorem endingRestriction_ι (p : Index F j) :
    endingRestriction F j p ≫ (SSet.ihomToPullbackFiber (oldLeftSquare F j p)).ι =
      (SSet.ihomToPullbackFiber (leftSquare F j p)).ι := by
  rw [endingRestriction, precompSquare_ι, MonoidalClosed.pre_id, NatTrans.id_app,
    Category.comp_id]

private theorem startingRestriction_ι (p : Index F j) :
    startingRestriction F j p ≫ (SSet.ihomToPullbackFiber (oldRightSquare F j p)).ι =
      (SSet.ihomToPullbackFiber (rightSquare F j p)).ι := by
  rw [startingRestriction, precompSquare_ι, MonoidalClosed.pre_id, NatTrans.id_app,
    Category.comp_id]

private theorem ending_map_ι {p q : (Index F j)ᵒᵖ} (α : p ⟶ q) :
    (endingSpaces F j).map α ≫ (SSet.ihomToPullbackFiber (leftSquare F j q.unop)).ι =
      (SSet.ihomToPullbackFiber (leftSquare F j p.unop)).ι ≫
        (MonoidalClosed.pre (std.map ((degrees F j).map α.unop))).app (row W ⦋1⦌) := rfl

private theorem starting_map_ι {p q : (Index F j)ᵒᵖ} (α : p ⟶ q) :
    (startingSpaces F j).map α ≫ (SSet.ihomToPullbackFiber (rightSquare F j q.unop)).ι =
      (SSet.ihomToPullbackFiber (rightSquare F j p.unop)).ι ≫
        (MonoidalClosed.pre (std.map ((degrees F j).map α.unop))).app (row W ⦋1⦌) := rfl

private theorem oldEnding_map_ι {p q : (Index F j)ᵒᵖ} (α : p ⟶ q) :
    (JTActualJointChoiceCover.endingSpaces F j).map α ≫
        (SSet.ihomToPullbackFiber (oldLeftSquare F j q.unop)).ι =
      (SSet.ihomToPullbackFiber (oldLeftSquare F j p.unop)).ι ≫
        (MonoidalClosed.pre (std.map ((degrees F j).map α.unop))).app (row W ⦋1⦌) := rfl

private theorem oldStarting_map_ι {p q : (Index F j)ᵒᵖ} (α : p ⟶ q) :
    (JTActualJointChoiceCover.startingSpaces F j).map α ≫
        (SSet.ihomToPullbackFiber (oldRightSquare F j q.unop)).ι =
      (SSet.ihomToPullbackFiber (oldRightSquare F j p.unop)).ι ≫
        (MonoidalClosed.pre (std.map ((degrees F j).map α.unop))).app (row W ⦋1⦌) := rfl

/-- Restrict every full incident-supported ending simplex to the existing actual vertex support. -/
def restrictEnding : endingSpaces F j ⟶ JTActualJointChoiceCover.endingSpaces F j where
  app p := endingRestriction F j p.unop
  naturality p q α := by
    apply (cancel_mono (SSet.ihomToPullbackFiber (oldLeftSquare F j q.unop)).ι).mp
    rw [Category.assoc, endingRestriction_ι, ending_map_ι,
      Category.assoc, oldEnding_map_ι, ← Category.assoc, endingRestriction_ι]

/-- Restrict every full incident-supported starting simplex in the same old coefficient. -/
def restrictStarting : startingSpaces F j ⟶ JTActualJointChoiceCover.startingSpaces F j where
  app p := startingRestriction F j p.unop
  naturality p q α := by
    apply (cancel_mono (SSet.ihomToPullbackFiber (oldRightSquare F j q.unop)).ι).mp
    rw [Category.assoc, startingRestriction_ι, starting_map_ι,
      Category.assoc, oldStarting_map_ι, ← Category.assoc, startingRestriction_ι]

/-- Paired restriction preserves both actual edges and their full common simplex degree. -/
def restriction : spaces F j ⟶ JTActualJointChoiceCover.spaces F j :=
  tensorNat (restrictEnding F j) (restrictStarting F j)

/-- The full actual ending-choice space is Kan for an injective-fibrant original target. -/
theorem endingSpaces_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (Index F j)ᵒᵖ) : ((endingSpaces F j).obj p).KanComplex :=
  JTSubcomplexRelativeChoiceDiagram.leftChoices_kan W (diagram F j) (degrees F j)
    (inclusion F j) (endpointRows F j) (z j) (JTIncidentBeadSupportData.row_on_support F j)
    hW (JTIncidentBeadSupportWeak.support_mono F j) p

/-- The full actual starting-choice space is Kan under the same fibrancy hypothesis. -/
theorem startingSpaces_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (Index F j)ᵒᵖ) : ((startingSpaces F j).obj p).KanComplex :=
  JTSubcomplexRelativeChoiceDiagram.rightChoices_kan W (diagram F j) (degrees F j)
    (inclusion F j) (endpointRows F j) (z j) (JTIncidentBeadSupportData.row_on_support F j)
    hW (JTIncidentBeadSupportWeak.support_mono F j) p

/-- Each actual paired space is weakly contractible, with no supplied support premise. -/
theorem spaces_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (Index F j)ᵒᵖ) : GW (pointMap ((spaces F j).obj p)) :=
  JTSubcomplexRelativeChoiceDiagram.pairChoices_point_GW W (diagram F j) (degrees F j)
    (inclusion F j) (endpointRows F j) (z j) (JTIncidentBeadSupportData.row_on_support F j)
    hW (JTIncidentBeadSupportWeak.support_mono F j)
    (JTIncidentBeadSupportWeak.support_weak F j) p

/-- All paired choices and all common higher simplex operators over the exact-cut source. -/
abbrev Cover := (totalDiagram (spaces F j)).Elementsᵒᵖ

/-- Forget only the paired choices and their higher simplex degree. -/
abbrev projection : Cover F j ⥤ Index F j :=
  (CategoryOfElements.π (totalDiagram (spaces F j)) ⋙
    CategoryTheory.Prod.fst (Index F j)ᵒᵖ SimplexCategoryᵒᵖ).leftOp

/-- The full incident-choice cover is weak over the original exactly marked diagram. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j)) := by
  let E := (totalDiagram (spaces F j)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff (projection F j)).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (totalDiagram (spaces F j)) ⋙
      CategoryTheory.Prod.fst (Index F j)ᵒᵖ SimplexCategoryᵒᵖ))
  exact SynchronizedSimplicialParameters.projection_weak (spaces F j)
    (spaces_point_GW F j hW)

/-- Restrict full paired simplices to the existing actual vertex-choice cover. -/
def toActual : Cover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  ((Functor.uncurry.map (restriction F j)).mapElements).op

/-- Restriction retains the exact original source cut and source operator. -/
theorem toActual_projection :
    toActual F j ⋙ JTActualJointChoiceCover.projection F j = projection F j := rfl

/-- Restriction retains every common higher simplicial choice operator. -/
theorem toActual_time :
    toActual F j ⋙ SynchronizedSimplicialParameters.time (JTActualJointChoiceCover.spaces F j) =
      SynchronizedSimplicialParameters.time (spaces F j) := rfl

end
end DaggerModels.PartII.JTIncidentBeadChoiceDiagram
