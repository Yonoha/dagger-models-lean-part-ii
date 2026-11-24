import DaggerModelsPartII.JTGraphVariableTotalParametrizedFamily
import DaggerModelsPartII.JTGraphVariableExactEvaluation
import DaggerModelsPartII.JTGraphVariableCoherentLiftComparison
import DaggerModelsPartII.JTBoundaryNecklaceAssembleTransport
import DaggerModelsPartII.JTBoundaryNecklaceSectionEvaluation

/-!
The existing full internal traversal is a section of the complete presentation
of the assembled global family. Keep the actual original internal necklaces,
rather than replacing them by a vertex or only a raw-value equality.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableTotalFamilyEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableResolutionCategory
open BoundaryNecklaceComma (necklaceUnder)
open JTGraphVariableTotalParametrizedFamily (family operators_map time_map)

noncomputable section

private def withoutIdentityTarget {A : Type} [SmallCategory A]
    {F C : A ⥤ Under JTXiEndpointCollapse.boundary}
    (m : F ⟶ 𝟭 A ⋙ C) : F ⟶ C := m

private theorem evaluateSectionIdentity
    {I A X : Type} [SmallCategory I] [SmallCategory A] [SmallCategory X]
    (E : I ⥤ Under JTXiEndpointCollapse.boundary)
    (C : A ⥤ Under JTXiEndpointCollapse.boundary) (L : A ⥤ I)
    (ρ : C ⟶ L ⋙ E) (N : A ⥤ NecklaceCode)
    (m : N ⋙ necklaceUnder ⟶ 𝟭 A ⋙ C)
    (H : BoundaryNecklaceComma.Presentation E ⥤ X)
    (s : N ⋙ necklaceUnder ⟶ L ⋙ E) (h : withoutIdentityTarget m ≫ ρ = s) :
    JTTargetCommaPullback.assemble C (𝟭 A) N m ⋙
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ H) =
      JTTargetCommaPullback.assemble E L N s ⋙ H :=
  JTBoundaryNecklaceSectionEvaluation.evaluate_section_of_eq E C L ρ N
    (withoutIdentityTarget m) H s h

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev cylinders := JTParametrizedTargetFamilies.cylinders
  (L := totalLabels Q) (time := JTGraphVariableTotalParametrizedFamily.time Q)

/-- The global family retains the old native/time cylinder operator exactly. -/
theorem cylinders_map {P P' : Total Q} (f : P ⟶ P') :
    (cylinders Q).map f =
      NecklaceCylinderJointDiagram.cylinderUnder.map ((totalJoint Q).map f) := by
  change NecklaceCylinderJointDiagram.cylinderUnder.map
      (show
        (((JTParametrizedTargetFamilies.codes (totalLabels Q)).obj P),
          (JTGraphVariableTotalParametrizedFamily.time Q).obj P) ⟶
        (((JTParametrizedTargetFamilies.codes (totalLabels Q)).obj P'),
          (JTGraphVariableTotalParametrizedFamily.time Q).obj P') from
        (((OrderedLabelElements.projection W
          (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
            ((totalLabels Q).map f)).1,
          (JTGraphVariableTotalParametrizedFamily.time Q).map f)) = _
  rw [operators_map, time_map, totalJoint_map]
  rfl

/-- Retain each original complete internal-necklace traversal in the
corresponding global family cylinder, naturally in every original operator. -/
def traversal : totalCode Q ⋙ necklaceUnder ⟶ 𝟭 (Total Q) ⋙ cylinders Q where
  app P := P.fiber.fiber.hom
  naturality {P P'} f := by
    change necklaceUnder.map ((totalCode Q).map f) ≫ P'.fiber.fiber.hom =
      P.fiber.fiber.hom ≫ (cylinders Q).map f
    rw [cylinders_map]
    exact (totalEvaluation Q).naturality f

/-- The section keeps the original internal necklace at every actual
object of the existing global resolution. -/
def sectionFunctor : Total Q ⥤
    JTParametrizedTargetFamilies.Presentation
      (L := totalLabels Q) (time := JTGraphVariableTotalParametrizedFamily.time Q) :=
  JTTargetCommaPullback.assemble (cylinders Q) (𝟭 (Total Q)) (totalCode Q) (traversal Q)

/-- The section projects to the identical original resolution index. -/
theorem section_forget : sectionFunctor Q ⋙
    Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (cylinders Q)) =
      𝟭 (Total Q) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro P P' f
  change f = eqToHom (rfl : P = P) ≫ f ≫ eqToHom (rfl : P' = P')
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem global_decorated (P : Total Q) :
    (JTParametrizedTargetFamilies.liftNatural (family Q)).app P ≫
        JTTargetCommaPullback.fst W x y Q ((totalLabels Q).obj P) =
      (JTGraphVariableTimeTraversal.decoratedNatural P.base).app P.fiber.base := by
  exact (JTParametrizedTargetLiftProjections.decorated (family Q) P).trans (by rfl)

private theorem global_native (P : Total Q) :
    (JTParametrizedTargetFamilies.liftNatural (family Q)).app P ≫
        JTTargetCommaPullback.snd W x y Q ((totalLabels Q).obj P) =
      (JTGraphVariableTimeTraversal.targetNatural P.base).app P.fiber.base := by
  exact (JTParametrizedTargetLiftProjections.native (family Q) P).trans (by rfl)

/-- The new family lift is the existing full two-leg fixed-target lift. -/
theorem lift_app (P : Total Q) :
    ((JTParametrizedTargetFamilies.liftNatural (family Q)).app P :
      NecklaceCylinderJointDiagram.cylinderUnder.obj ((totalJoint Q).obj P) ⟶
        (JTTargetCommaPullback.diagram W x y Q).obj ((totalLabels Q).obj P)) =
    ((totalLift Q).app P :
      NecklaceCylinderJointDiagram.cylinderUnder.obj ((totalJoint Q).obj P) ⟶
        (JTTargetCommaPullback.diagram W x y Q).obj ((totalLabels Q).obj P)) := by
  apply pullback.hom_ext
    (f := (DecoratedCylinderNecklacePresentation.underCocone W x y).app
      ((totalLabels Q).obj P))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · exact (global_decorated Q P).trans
      (JTGraphVariableLiftProjections.lift_fst P.base P.fiber.base).symm
  · exact (global_native Q P).trans
      (JTGraphVariableLiftProjections.lift_snd P.base P.fiber.base).symm


private def plainTraversal : totalCode Q ⋙ necklaceUnder ⟶ cylinders Q :=
  withoutIdentityTarget (traversal Q)

private theorem traversal_lift_app (P : Total Q) :
    ((plainTraversal Q ≫ JTParametrizedTargetFamilies.liftNatural (family Q)).app P :
      necklaceUnder.obj ((totalCode Q).obj P) ⟶
        (JTTargetCommaPullback.diagram W x y Q).obj ((totalLabels Q).obj P)) =
    ((totalEvaluation Q ≫ totalLift Q).app P :
      necklaceUnder.obj ((totalCode Q).obj P) ⟶
        (JTTargetCommaPullback.diagram W x y Q).obj ((totalLabels Q).obj P)) := by
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext n
  funext t
  exact congrArg
    (fun h : NecklaceCylinderJointDiagram.cylinderUnder.obj ((totalJoint Q).obj P) ⟶
        (JTTargetCommaPullback.diagram W x y Q).obj ((totalLabels Q).obj P) ↦
      h.right.app n (P.fiber.fiber.hom.right.app n t)) (lift_app Q P)

private theorem traversal_lift :
    plainTraversal Q ≫ JTParametrizedTargetFamilies.liftNatural (family Q) =
      totalEvaluation Q ≫ totalLift Q := by
  apply NatTrans.ext
  funext P
  exact traversal_lift_app Q P

/-- The full section evaluates by the already constructed original fixed-Q
functor, retaining every internal necklace and every original arrow. -/
theorem section_evaluate :
    sectionFunctor Q ⋙ JTParametrizedTargetFamilies.evaluate (family Q) =
      JTGraphVariableExactEvaluation.evaluation Q := by
  exact evaluateSectionIdentity
    (JTTargetCommaPullback.diagram W x y Q) (cylinders Q) (totalLabels Q)
    (JTParametrizedTargetFamilies.liftNatural (family Q)) (totalCode Q) (traversal Q)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)
    (totalEvaluation Q ≫ totalLift Q) (traversal_lift Q)

/-- The genuine global-family section compares naturally to the original
comma diagram, using the old exact full-evaluation comparison. -/
def comparison : sectionFunctor Q ⋙ JTParametrizedTargetFamilies.evaluate (family Q) ⟶
    Grothendieck.forget (JTGraphVariableTimeTransport.resolutionDiagram Q) :=
  (eqToHom (section_evaluate Q)) ≫ JTGraphVariableExactEvaluation.comparison Q

end
end DaggerModels.PartII.JTGraphVariableTotalFamilyEvaluation
