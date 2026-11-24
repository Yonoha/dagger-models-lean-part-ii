import DaggerModelsPartII.JTParametrizedTargetFamilies

/-! The exact parametrized evaluation preserves the native and decorated operators. -/

set_option autoImplicit false
set_option maxHeartbeats 300000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetFamilies

open JTProjectiveOrderedFiberComparison (row)
open JTTargetCommaExactEvaluation (fromPresentation)
open JTTargetCommaPullback (toPullback toPullback_map_operators)
open JTTargetCommaPullbackSliceProjection (comparison_arrow pair_fromObj)
open JTBoundaryNecklacePresentationCone (mapPresentation mapPresentation_code)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev G := JTTargetCommaPullback.Presentation W x y Q
private abbrev C := JTTargetCommaPullback.diagram W x y Q

/-- Leaving a paired presentation preserves its prescribed decorated and native operators. -/
theorem fromPresentation_map_operators {R S : G Q} (f : R ⟶ S) :
    ((fromPresentation W x y Q).map f).left.base = f.base ∧
    ((fromPresentation W x y Q).map f).left.fiber.left = f.fiber.left := by
  have he := comparison_arrow W x y Q f
  change (toPullback W x y Q).map ((fromPresentation W x y Q).map f) =
    eqToHom (pair_fromObj W x y Q R) ≫ f ≫ eqToHom (pair_fromObj W x y Q S).symm at he
  obtain ⟨hb, hc⟩ := toPullback_map_operators W x y Q ((fromPresentation W x y Q).map f)
  constructor
  · have h := congrArg (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (C Q))).map he
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map] at h
    change ((toPullback W x y Q).map ((fromPresentation W x y Q).map f)).base =
      𝟙 R.base ≫ f.base ≫ 𝟙 S.base at h
    rw [hb, Category.id_comp, Category.comp_id] at h
    exact h
  · have h := congrArg (BoundaryNecklaceComma.sourceCode (C Q)).map he
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map] at h
    change ((toPullback W x y Q).map ((fromPresentation W x y Q).map f)).fiber.left =
      𝟙 R.fiber.left ≫ f.fiber.left ≫ 𝟙 S.fiber.left at h
    rw [hc, Category.id_comp, Category.comp_id] at h
    exact h

variable {Q} {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time)

private abbrev paired := mapPresentation (C Q) (cylinders (L := L) (time := time)) L (liftNatural F)

private theorem mapped_operators
    {D : A ⥤ Under JTXiEndpointCollapse.boundary} (r : D ⟶ L ⋙ C Q)
    {P P' : BoundaryNecklaceComma.Presentation D} (f : P ⟶ P') :
    ((mapPresentation (C Q) D L r ⋙ fromPresentation W x y Q).map f).left.base =
      L.map f.base ∧
    ((mapPresentation (C Q) D L r ⋙ fromPresentation W x y Q).map f).left.fiber.left =
      f.fiber.left := by
  let p := mapPresentation (C Q) D L r
  have h := fromPresentation_map_operators Q (p.map f)
  have hc : (p.map f).fiber.left = f.fiber.left := mapPresentation_code (C Q) D L r f
  exact ⟨h.1, h.2.trans hc⟩

set_option maxHeartbeats 1800000 in
/-- The exact evaluation uses the original decorated label arrow and the entire internal
necklace operator, including operators that collapse beads. -/
theorem evaluate_map_operators {P P' : Presentation (L := L) (time := time)} (f : P ⟶ P') :
    ((evaluate F).map f).left.base = L.map f.base ∧
    ((evaluate F).map f).left.fiber.left = f.fiber.left :=
  @mapped_operators W x y Q A _ L (cylinders (L := L) (time := time)) (liftNatural F) P P' f

open JTParametrizedTargetLiftTransport (graph)
open NecklaceCylinderAugmentation (augmentation)

/-- On each whole internal necklace the decorated leg is the original full graph map. -/
theorem evaluate_decorated (P : Presentation (L := L) (time := time)) :
    ((evaluate F).obj P).left.fiber.hom.right =
      P.fiber.hom.right ≫ (graph (F.parameter P.base)).right := by
  let h := (JTTargetCommaExactEvaluation.decorated_map_obj W x y Q ((paired F).obj P))
  have h' := congrArg (fun f ↦ f.right) h
  change _ = (P.fiber.hom ≫ (liftNatural F).app P.base ≫
    JTTargetCommaPullback.fst W x y Q (L.obj P.base)).right at h'
  rw [show (liftNatural F).app P.base ≫ JTTargetCommaPullback.fst W x y Q (L.obj P.base) =
      graph (F.parameter P.base) from JTCylinderOverTarget.lift_decorated W x y Q _ _ _
        _ _ (F.raw P.base)] at h'
  exact h'

/-- On each whole internal necklace the native leg is its augmentation and given collapse. -/
theorem evaluate_native (P : Presentation (L := L) (time := time)) :
    ((evaluate F).obj P).hom.hom.map =
      P.fiber.hom.right ≫ augmentation ((codes L).obj P.base) (time.obj P.base) ≫
        (F.collapse.app P.base).map := by
  let h := JTTargetCommaExactEvaluation.native_map_obj W x y Q ((paired F).obj P)
  have h' := congrArg (fun f ↦ f.right) h
  change _ = (P.fiber.hom ≫ (liftNatural F).app P.base ≫
    JTTargetCommaPullback.snd W x y Q (L.obj P.base)).right at h'
  rw [show (liftNatural F).app P.base ≫ JTTargetCommaPullback.snd W x y Q (L.obj P.base) =
      JTCylinderOverTarget.native W x y Q _ _ (F.collapse.app P.base) from
    JTCylinderOverTarget.lift_native W x y Q _ _ _ _ _ (F.raw P.base)] at h'
  exact h'

end
end DaggerModels.PartII.JTParametrizedTargetFamilies
