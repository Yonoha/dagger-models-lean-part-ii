import DaggerModelsPartII.JTGraphInterpolatedOverOriginal
import DaggerModelsPartII.JTTargetCommaPullbackSliceExt

/-!
# Exact time-slice maps over the original comma object
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedOverOriginalSlice

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphInterpolatedComparison (Fiber comparisonFunctor comparison_slice_iso sliceObject)
open JTCommaGraphPredecessor (augmentationCode)
open NecklaceCylinderAugmentation (augmentation)
open JTTargetCommaPullback (diagram toPullback equivalence)
open JTGraphInterpolatedCollapseOriginal
open JTGraphInterpolatedOverOriginal

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)

private theorem map_to_original {C G : Type*} [Category* C] [Category* G] (e : C ≌ G)
    {X U : C} {P : G} (h : e.functor.obj X = P) (f : P ⟶ e.functor.obj U) :
    e.functor.map
      (((e.inverse.mapIso (eqToIso h.symm)).trans (e.unitIso.app X).symm).inv ≫
        e.inverse.map f ≫ (e.unitIso.app U).inv) =
      eqToHom h ≫ f := by
  cases h
  simp only [eqToIso_refl, Functor.mapIso_refl, Iso.refl_trans, Iso.symm_inv,
    eqToHom_refl, Category.id_comp, Functor.map_comp]
  change e.functor.map (e.unit.app X) ≫ e.functor.map (e.inverse.map f) ≫
    e.functor.map (e.unitInv.app U) = f
  rw [← e.counitInv_app_functor X, ← e.counit_app_functor U,
    ← Category.assoc, e.counitInv_naturality]
  simp

private theorem map_left_cast_heq {C G : Type*} [Category* C] [Category* G]
    (F : C ⥤ G) {A A' B : C} (h : A = A') (f : A' ⟶ B) :
    HEq (F.map (eqToHom h ≫ f)) (F.map f) := by
  subst A'
  simp only [eqToHom_refl, Category.id_comp]
  rfl

private theorem to_original_eq_of_operators
    {P : JTTargetCommaPullback.Presentation W x y Q}
    {X : TargetComma Q} (h : JTTargetCommaPullback.fromObj W x y Q P = X)
    (f : P ⟶ (toPullback W x y Q).obj U) (g : X ⟶ U)
    (hb : HEq ((JTTargetCommaPullbackSliceExt.decoratedProjection W x y Q).map f)
      ((JTTargetCommaPullbackSliceExt.decoratedProjection W x y Q).map
        ((toPullback W x y Q).map g)))
    (hc : HEq ((BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map f)
      ((BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map ((toPullback W x y Q).map g))) :
    ((JTTargetCommaPullbackSliceProjection.comparisonIso W x y Q P).trans (eqToIso h)).inv ≫
        (equivalence W x y Q).inverse.map f ≫ ((equivalence W x y Q).unitIso.app U).inv = g := by
  subst X
  simp only [eqToIso_refl, Iso.trans_refl]
  apply (equivalence W x y Q).functor.map_injective
  unfold JTTargetCommaPullbackSliceProjection.comparisonIso
  let H := JTTargetCommaPullbackSliceProjection.pair_fromObj W x y Q P
  rw [map_to_original (equivalence W x y Q) H f]
  have hBase := eq_of_heq
    ((map_left_cast_heq (JTTargetCommaPullbackSliceExt.decoratedProjection W x y Q) H f).trans hb)
  have hCode := eq_of_heq
    ((map_left_cast_heq (BoundaryNecklaceComma.sourceCode (diagram W x y Q)) H f).trans hc)
  apply JTTargetCommaPullback.operator_ext (hc := hCode)
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun t ↦ t.op) hBase

/-- The cone at a time vertex is exactly the graph predecessor's original map. -/
theorem comparisonToOriginal_slice (i : Fin (n.len + 1)) :
    (comparison_slice_iso c D hD i).inv ≫
      (comparisonToOriginal c D hD).app (sliceObject S n i) =
    JTGraphTransportNaturality.toComma (D i) := by
  let f := (presentationCone c D hD).app (sliceObject S n i)
  let L := JTTargetCommaPullbackSliceExt.decoratedProjection W x y Q
  let N := BoundaryNecklaceComma.sourceCode (diagram W x y Q)
  have hBase : L.map f = (c ≫ augmentationCode U.left, 𝟙 (degree U.left)) := by
    change (projection (W := W) (x := x) (y := y)).map f.base = _
    rw [show f.base = indexCollapse c D hD from
      JTBoundaryNecklacePresentationCone.cone_base _ _ _ _ _ _ _,
      indexCollapse_operator]
  have hCode : N.map f = c := by
    apply NecklaceCode.Hom.ext
    change f.fiber.left.map = c.map
    rw [show f.fiber.left.map = ((sliceObject S n i).hom ≫ timeCollapse c).right from
      JTBoundaryNecklacePresentationCone.cone_native_map _ _ _ _ _ _ _]
    change (JTInterpolatedReducedCylinder.slice S n i).right ≫ augmentation S n ≫ c.map =
      c.map
    rw [← Category.assoc, JTInterpolatedReducedCylinder.slice_augmentation]
    exact Category.id_comp _
  have hBase' : L.map ((toPullback W x y Q).map (JTGraphTransportNaturality.toComma (D i))) =
      ((D i).collapse ≫ augmentationCode U.left, 𝟙 (degree U.left)) := rfl
  have hCode' : N.map ((toPullback W x y Q).map (JTGraphTransportNaturality.toComma (D i))) =
      (D i).collapse := rfl
  rw [hD i] at hBase' hCode'
  unfold comparisonToOriginal
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.constComp_hom_app,
    Functor.const_map_app, Category.id_comp]
  change (comparison_slice_iso c D hD i).inv ≫
      ((equivalence W x y Q).inverse.map f ≫ ((equivalence W x y Q).unitIso.app U).inv) = _
  unfold comparison_slice_iso
  rw [JTTargetCommaPullbackSliceProjection.existingIso_eq]
  -- Use the equality witness carried by the canonical slice isomorphism.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.instantiateMVars (← goal.getType)
    let (_, lhs, _) ← target.consumeMData.eq?.getDM (throwError "Expected a slice arrow equality")
    let args := lhs.consumeMData.getAppArgs
    let first ← args[args.size - 2]?.getDM (throwError "Expected the slice arrow")
    let equalityIso ← (first.find? (·.isAppOfArity ``eqToIso 5)).getDM
      (throwError "Expected a slice equality isomorphism")
    let (_, goal) ←
      (← goal.assert `sliceEquality (← Lean.Meta.inferType equalityIso.appArg!)
        equalityIso.appArg!).intro1P
    Lean.Elab.Tactic.replaceMainGoal [goal]
  exact to_original_eq_of_operators sliceEquality
    f (JTGraphTransportNaturality.toComma (D i))
    (heq_of_eq (hBase.trans hBase'.symm)) (heq_of_eq (hCode.trans hCode'.symm))

set_option maxHeartbeats 400000 in
/-- The original graph predecessor, with its original arrow to the comma
object, is the canonical slice of the entire comparison over that object. -/
def overOriginal_slice_iso (i : Fin (n.len + 1)) :
    (overOriginal c D hD).obj (sliceObject S n i) ≅
      Over.mk (JTGraphTransportNaturality.toComma (D i)) :=
  Over.isoMk (comparison_slice_iso c D hD i) (by
    change (comparison_slice_iso c D hD i).hom ≫ JTGraphTransportNaturality.toComma (D i) =
      (comparisonToOriginal c D hD).app (sliceObject S n i)
    rw [← comparisonToOriginal_slice c D hD i, Iso.hom_inv_id_assoc])

end

end DaggerModels.PartII.JTGraphInterpolatedOverOriginalSlice
