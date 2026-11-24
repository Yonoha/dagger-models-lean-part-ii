import DaggerModelsPartII.JTGraphVariableComparisonTransport
import DaggerModelsPartII.JTBoundaryNecklacePresentationTransport

/-! Transport of the complete comparison along original comma arrows. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableComparisonAlong

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex (Index joint Resolution)
open JTGraphVariableTimeTransport (transport transport_joint transportResolution)
open JTGraphVariableTimeTraversal (labels)
open JTGraphVariableTimeComparison (liftNatural toComma)
open JTGraphVariableLabelTransport (labelTransport)
open JTGraphVariableComparisonTransport (lift_square_heq)
open JTBoundaryNecklacePresentationTransport (preJoint comparisonJoint)
open JTBoundaryNecklacePresentationCone (mapPresentation)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : @TargetComma W x y Q} (a : U ⟶ V)

private abbrev indexAt (A : @TargetComma W x y Q) := @Index W x y Q A
private abbrev jointAt (A : @TargetComma W x y Q) := @joint W x y Q A
private abbrev labelsAt (A : @TargetComma W x y Q) := @labels W x y Q A
private abbrev liftAt (A : @TargetComma W x y Q) := @liftNatural W x y Q A
private abbrev mapToComma (A : @TargetComma W x y Q) := @toComma W x y Q A
private abbrev transportIndex := @transport W x y Q U V a
private abbrev transportLabels := @labelTransport W x y Q U V a
private abbrev wholeTransport := @transportResolution W x y Q U V a
private abbrev E := JTTargetCommaPullback.diagram W x y Q
private abbrev T := NecklaceCylinderJointDiagram.cylinderUnder

private def preAlong : @Resolution W x y Q U ⥤ @Resolution W x y Q V :=
  @preJoint (indexAt V) _ (indexAt U) (NecklaceCode × SimplexCategory) _ _
    (transportIndex a) (jointAt V) (jointAt U) (T ⋙ BoundaryNecklaceComma.diagram)
    (@transport_joint W x y Q U V a)

private theorem pre_eq_transport : preAlong a = wholeTransport a := rfl

private abbrev presented (A : @TargetComma W x y Q) :=
  JTBoundaryNecklacePresentationCone.mapPresentation (E (Q := Q)) (jointAt A ⋙ T)
    (labelsAt A) (liftAt A) ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse

private theorem presentation_eq (A : @TargetComma W x y Q) :
    mapToComma A = presented A := rfl

-- Compare using the underlying simplicial maps so that the kernel does not
-- have to reduce the pullback morphism types during specialization.
private def comparisonJointOnRight {I J K R C : Type}
    [SmallCategory I] [SmallCategory J] [SmallCategory K] [SmallCategory R] [SmallCategory C]
    (E : I ⥤ Under JTXiEndpointCollapse.boundary) (G : K ⥤ J) (A : J ⥤ R) (A₀ : K ⥤ R)
    (T : R ⥤ Under JTXiEndpointCollapse.boundary) (hJoint : G ⋙ A = A₀)
    {L : J ⥤ I} {M : K ⥤ I}
    (p₁ : A ⋙ T ⟶ L ⋙ E) (p₀ : A₀ ⋙ T ⟶ M ⋙ E) (α : M ⟶ G ⋙ L)
    (h : ∀ i, HEq ((p₀.app i).right ≫ (E.map (α.app i)).right) (p₁.app (G.obj i)).right)
    (H : BoundaryNecklaceComma.Presentation E ⥤ C) :
    mapPresentation E (A₀ ⋙ T) M p₀ ⋙ H ⟶
      preJoint G A A₀ (T ⋙ BoundaryNecklaceComma.diagram) hJoint ⋙
        mapPresentation E (A ⋙ T) L p₁ ⋙ H := by
  subst A₀
  apply comparisonJoint E G A (G ⋙ A) T rfl p₁ p₀ α _ H
  intro i
  apply heq_of_eq
  apply Under.UnderMorphism.ext
  exact eq_of_heq (h i)

set_option maxHeartbeats 28000 in
private theorem comparisonSquareRight (P : indexAt U) :
    HEq (((liftAt U).app P).right ≫ ((E (Q := Q)).map ((transportLabels a).app P)).right)
      ((liftAt V).app ((transportIndex a).obj P)).right := by
  have h := @lift_square_heq W x y Q U V a P
  have he := eq_of_heq h
  exact heq_of_eq (congrArg (fun f ↦ f.right) he)

set_option maxHeartbeats 28000 in
private def comparisonOnRight :=
  @comparisonJointOnRight (DecoratedNecklaceHomDiagram.Index W x y) (indexAt V)
    (indexAt U) (NecklaceCode × SimplexCategory) (TargetComma Q) _ _ _ _ _ (E (Q := Q))
    (transportIndex a) (jointAt V) (jointAt U) T (@transport_joint W x y Q U V a)
    (labelsAt V) (labelsAt U) (liftAt V) (liftAt U) (transportLabels a)
    (comparisonSquareRight a) (JTTargetCommaPullback.equivalence W x y Q).inverse

private theorem out_eq : preAlong a ⋙ presented V = wholeTransport a ⋙ mapToComma V :=
  (congrArg (· ⋙ presented V) (pre_eq_transport a)).trans
    (congrArg (wholeTransport a ⋙ ·) (presentation_eq V).symm)

set_option maxHeartbeats 28000 in
/-- Compare both maps of the entire resolutions into the original fixed-target comma. -/
def comparisonTransport : mapToComma U ⟶ wholeTransport a ⋙ mapToComma V :=
  eqToHom (presentation_eq U) ≫ comparisonOnRight a ≫ eqToHom (out_eq a)

end
end DaggerModels.PartII.JTGraphVariableComparisonAlong
