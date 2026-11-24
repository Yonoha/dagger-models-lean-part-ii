import DaggerModelsPartII.JTGraphLiftRestriction
import DaggerModelsPartII.JTGraphPresentationOperator
import DaggerModelsPartII.JTGraphSingleBeadNormalization

/-!
# Native restriction arrows over a fixed raw necklace target
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphRestrictionRaw

open JTProjectiveOrderedFiberComparison OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open JTGraphLiftTransport JTGraphLiftRestriction
open JTCommaGraphPredecessor (augmentationCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev F (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  DecoratedCylinderNecklacePresentation.toTarget W x y

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P : Pres (W := W) (x := x) (y := y)} {S T : NecklaceCode}

private abbrev horizontal (E : GraphLift P T) := E.collapse ≫ augmentationCode P
private abbrev label (E : GraphLift P T) :=
  JTGraphToPresentationArrow.pulledLabel P T (horizontal E)
private abbrev graph (E : GraphLift P T) :=
  JTGraphToPresentationArrow.graphPresentation P T (horizontal E) E.parameter
private theorem horizontal_restrict (E : GraphLift P T) (g : S ⟶ T) :
    horizontal (restrict E g) = g ≫ horizontal E :=
  Category.assoc _ _ _

private theorem label_restrict (E : GraphLift P T) (g : S ⟶ T) :
    let L := orderedNecklaceLabels W (boundaryPoint W x y)
    (L.map g.op).app (op (degree P)) (label E) = label (restrict E g) := by
  dsimp only
  let L := orderedNecklaceLabels W (boundaryPoint W x y)
  let z := OrderedLabelElements.label W (boundaryPoint W x y) P.base
  change (L.map g.op).app (op (degree P))
      ((L.map (horizontal E).op).app (op (degree P)) z) =
    (L.map (horizontal (restrict E g)).op).app (op (degree P)) z
  rw [horizontal_restrict E g]
  simp only [op_comp, Functor.map_comp]
  conv_rhs =>
    rw [NatTrans.comp_app, NatTrans.comp_app]
  rw [NatTrans.comp_app]
  rfl

/-- A restriction arrow of actual graph presentations, at unchanged degree. -/
def restrictionArrow (E : GraphLift P T) (g : S ⟶ T) :
    graph (restrict E g) ⟶ graph E :=
  JTGraphPresentationOperator.presentationArrow g (𝟙 (degree P))
    (label (restrict E g)) (label E) (restrict E g).parameter E.parameter
    (by simpa only [op_id, CategoryTheory.Functor.map_id, types_id_apply] using
      label_restrict E g)
    (by
      rw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _)

theorem restrictionArrow_base (E : GraphLift P T) (g : S ⟶ T) :
    (projection (W := W) (x := x) (y := y)).map (restrictionArrow E g).base =
      (g, 𝟙 (degree P)) := rfl

theorem restrictionArrow_code (E : GraphLift P T) (g : S ⟶ T) :
    (restrictionArrow E g).fiber.left = g := rfl

variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : CostructuredArrow (F W x y) Q}

/-- The graph predecessor in the fixed raw target. -/
abbrev predecessor (E : GraphLift U.left T) :
    CostructuredArrow (F W x y) Q :=
  JTGraphToPresentationArrow.graphToComma U T (horizontal E) E.collapse
    E.parameter E.comm

/-- Restriction is an actual comma arrow; its native map is the prescribed `g`. -/
def commaRestriction (E : GraphLift U.left T) (g : S ⟶ T) :
    predecessor (restrict E g) ⟶ predecessor E := by
  refine CostructuredArrow.homMk (restrictionArrow E g) ?_
  apply NecklacesOver.Hom.ext
  change ((F W x y).map (restrictionArrow E g)).hom ≫
      (E.collapse ≫ U.hom.hom) =
    (restrict E g).collapse ≫ U.hom.hom
  rw [DecoratedCylinderNecklacePresentation.toTarget_map_hom]
  change g ≫ (E.collapse ≫ U.hom.hom) =
    (g ≫ E.collapse) ≫ U.hom.hom
  exact (Category.assoc _ _ _).symm

theorem commaRestriction_code (E : GraphLift U.left T) (g : S ⟶ T) :
    (commaRestriction E g).left.fiber.left = g := rfl

/-- Every one-bead graph lift has an actual raw comma arrow to the same
identity-collapse predecessor. -/
theorem exists_identity_raw_comparisons {d : ℕ}
    (hP : U.left.fiber.left = NecklaceCode.single d)
    (ht : NecklaceCode.first.{0} (code U.left) ≠ NecklaceCode.last.{0} (code U.left)) :
    ∃ E : GraphLift U.left U.left.fiber.left, E.collapse = 𝟙 _ ∧
      ∀ (e : ℕ) (D : GraphLift U.left (NecklaceCode.single e)),
        Nonempty (predecessor D ⟶ predecessor E) := by
  obtain ⟨E, hE, hD⟩ :=
    JTGraphSingleBeadNormalization.exists_identity_normalization hP ht
  refine ⟨E, hE, ?_⟩
  intro e D
  rw [hD e D]
  exact ⟨commaRestriction E D.collapse⟩

end

end DaggerModels.PartII.JTGraphRestrictionRaw
