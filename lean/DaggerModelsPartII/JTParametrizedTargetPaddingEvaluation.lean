import DaggerModelsPartII.JTParametrizedTargetCoefficientPadding
import DaggerModelsPartII.JTBoundaryNecklacePresentationTransport

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetCoefficientPadding

open JTOrderedLabelCoefficientPadding
open JTParametrizedTargetFamilies (Family codes cylinders liftNatural evaluate)
open JTBoundaryNecklacePresentationTransport (comparison)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time)

private abbrev C (L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y))
    (time : A ⥤ SimplexCategory) := cylinders (L := base L ⋙ L) (time := base L ⋙ time)

theorem sameCylinders (L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y))
    (time : A ⥤ SimplexCategory) :
    C L time = cylinders (L := labels L) (time := base L ⋙ time) := rfl

private abbrev E := JTTargetCommaPullback.diagram W x y Q

private def targetLift : C L time ⟶ labels L ⋙ E (Q := Q) := by
  rw [sameCylinders]
  exact liftNatural (paddedFamily F)

private theorem targetLift_app (p : Extensions L) :
    (targetLift F).app p = (liftNatural (paddedFamily F)).app p := by
  simp only [targetLift, eq_mpr_eq_cast, cast_eq]

/-- The presentations over the same shifted coefficient diagram compare naturally. -/
def evaluationComparison :
    evaluate (F.precomp (base L)) ⟶ evaluate (L := labels L) (paddedFamily F) := by
  let r := JTOrderedLabelCoefficientPadding.comparison L
  let p₀ : C L time ⟶ (base L ⋙ L) ⋙ E (Q := Q) := liftNatural (F.precomp (base L))
  let p₁ := targetLift F
  let d := JTTargetCommaExactEvaluation.fromPresentation W x y Q
  have h (p : Extensions L) : p₀.app p ≫ (E (Q := Q)).map (r.app p) = p₁.app p :=
    (comparison_lifts F p).trans (targetLift_app F p).symm
  have he : p₁ = liftNatural (paddedFamily F) := by
    apply NatTrans.ext
    funext p
    exact targetLift_app F p
  exact Functor.whiskerRight (comparison (E (Q := Q)) (C L time) p₀ p₁ r h) d ≫
    eqToHom (by
      change JTBoundaryNecklacePresentationCone.mapPresentation (E (Q := Q)) (C L time)
        (labels L) p₁ ⋙ d = _
      rw [he]
      rfl)

end
end DaggerModels.PartII.JTParametrizedTargetCoefficientPadding
