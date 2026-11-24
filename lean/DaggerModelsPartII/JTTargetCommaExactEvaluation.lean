import DaggerModelsPartII.JTTargetCommaPullbackSliceProjection
import DaggerModelsPartII.JTGraphCylinderSpanProjection

/-! The actual evaluation from paired presentations back to the original comma. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetCommaExactEvaluation

open JTTargetCommaPullback JTTargetCommaPullbackSliceProjection
open JTGraphFactoredPresentation (TargetComma)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev e := equivalence W x y Q

/-- Evaluate a whole pullback presentation with the specified native and decorated legs. -/
def fromPresentation : JTTargetCommaPullback.Presentation W x y Q ⥤ TargetComma Q :=
  (e W x y Q).inverse.copyObj (fromObj W x y Q) (comparisonIso W x y Q)

/-- The actual evaluated objects are the prescribed two-leg projections. -/
theorem fromPresentation_obj (P : JTTargetCommaPullback.Presentation W x y Q) :
    (fromPresentation W x y Q).obj P = fromObj W x y Q P := rfl

/-- The actual evaluation is naturally isomorphic to the existing inverse equivalence. -/
def inverseIso : (e W x y Q).inverse ≅ fromPresentation W x y Q :=
  (e W x y Q).inverse.isoCopyObj _ _

/-- The paired presentation is recovered exactly as a functor from the original comma. -/
theorem fromPresentation_comp :
    fromPresentation W x y Q ⋙ toPullback W x y Q = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (pair_fromObj W x y Q) ?_
  intro P P' f
  exact comparison_arrow W x y Q f

/-- The evaluated decorated map is the entire first projection. -/
theorem decorated_map_obj (P : JTTargetCommaPullback.Presentation W x y Q) :
    ((fromPresentation W x y Q).obj P).left.fiber.hom =
      P.fiber.hom ≫ fst W x y Q P.base := rfl

/-- The evaluated native morphism to the fixed target is the entire second projection. -/
theorem native_map_obj (P : JTTargetCommaPullback.Presentation W x y Q) :
    necklaceUnder.map ((fromPresentation W x y Q).obj P).hom.hom =
      P.fiber.hom ≫ snd W x y Q P.base :=
  map_nativeArrow _

end
end DaggerModels.PartII.JTTargetCommaExactEvaluation
