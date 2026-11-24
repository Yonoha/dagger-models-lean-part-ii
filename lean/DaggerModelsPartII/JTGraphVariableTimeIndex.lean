import DaggerModelsPartII.JTGraphParameterTimeResolution
import DaggerModelsPartII.JTGraphLiftRestriction
import DaggerModelsPartII.JTGraphCylinderFiberDiagram
import DaggerModelsPartII.TotalElementsWeakComparison

/-! All native source necklaces and exact time families over an original comma object. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphVariableTimeIndex

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport JTGraphLiftRestriction JTGraphParameterTimeResolution

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q)

/-- The actual slice of native codes over the internal necklace of the original object. -/
abbrev NativeSlice := Over U.left.fiber.left

private def restrictLift {P P' : NativeSlice U} (f : P ⟶ P') (D : Lifts U P'.hom) :
    Lifts U P.hom :=
  ⟨restrict D.val f.left, (congrArg (f.left ≫ ·) D.property).trans (Over.w f)⟩

/-- Exact graph parameters restrict contravariantly along every original native arrow. -/
def timeDiagram : (NativeSlice U)ᵒᵖ ⥤ SSet.{0} where
  obj P := timeSpace U P.unop.hom
  map f :=
    { app := fun _ D i ↦ restrictLift U f.unop (D i)
      naturality := by intros; rfl }
  map_id P := by
    apply NatTrans.ext
    funext n D i
    apply Subtype.ext
    exact restrict_id (D i).val
  map_comp f g := by
    apply NatTrans.ext
    funext n D i
    apply Subtype.ext
    exact (restrict_comp (D i).val g.unop.left f.unop.left).symm

/-- Every native collapse has a graph parameter, including the added degenerate beads. -/
theorem lifts_nonempty (P : NativeSlice U) : Nonempty (Lifts U P.hom) := by
  obtain ⟨E, hE⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift U.left
  refine ⟨⟨restrict E P.hom, ?_⟩⟩
  change P.hom ≫ E.collapse = P.hom
  rw [hE]
  exact Category.comp_id P.hom

private theorem time_point_GW (P : NativeSlice U) : GW (pointMap (timeSpace U P.hom)) :=
  (JTHomotopyTargetTimeResolution.point_GW_iff _ _).mp
    (resolution_point_GW U P.hom (lifts_nonempty U P).some)

private theorem point_of_op {D : Type} [SmallCategory D]
    (h : GW (pointMap (nerve Dᵒᵖ))) : GW (pointMap (nerve D)) := by
  let i := DaggerNativeNerveOppositeIso.nerveOppositeIso D
  letI : SSet.opFunctor.{0}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let ht := IsTerminal.isTerminalObj SSet.opFunctor.{0} _ pointIsTerminal
  let t := ht.uniqueUpToIso pointIsTerminal
  haveI : WeakEquivalence (pointMap (nerve Dᵒᵖ)) := (weakEquivalence_iff_GW _).mpr h
  apply (weakEquivalence_iff_GW _).mp
  apply (DaggerNativeSimplicialOppositeKanWeak.weak_op_iff _).mp
  rw [ht.hom_ext (SSet.opFunctor.map (pointMap (nerve D)))
    (i.hom ≫ pointMap (nerve Dᵒᵖ) ≫ t.inv)]
  infer_instance

private theorem elements_point_GW (P : NativeSlice U) :
    GW (pointMap (nerve (timeSpace U P.hom).Elements)) := by
  apply point_of_op
  let X := timeSpace U P.hom
  let a := SimplicialResolutionFunctor.augmentation.app X
  let e := SimplicialResolutionFunctor.elementsProjection.app X
  letI : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak X
  letI : WeakEquivalence e := SimplicialResolutionFunctor.elementsProjection_weak X
  letI : WeakEquivalence (pointMap X) := (weakEquivalence_iff_GW _).mpr (time_point_GW U P)
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff e _).mp
  rw [pointIsTerminal.hom_ext (e ≫ pointMap (nerve X.Elementsᵒᵖ)) (a ≫ pointMap X)]
  infer_instance

private abbrev G := GrothendieckTotalElements.totalDiagram (timeDiagram U)

/-- Objects keep the original native collapse and the full exact time family. -/
abbrev Index := (G U).Elementsᵒᵖ

/-- The covariant native slice operator of an original joint morphism. -/
abbrev toNative : Index U ⥤ NativeSlice U :=
  (CategoryOfElements.π (G U) ⋙ CategoryTheory.Prod.fst _ _).leftOp

/-- The exact time operator of an original joint morphism. -/
abbrev degree : Index U ⥤ SimplexCategory :=
  (CategoryOfElements.π (G U) ⋙ CategoryTheory.Prod.snd _ _).leftOp

/-- The original source necklace and time degree, with both actual operators. -/
def joint : Index U ⥤ NecklaceCode × SimplexCategory :=
  (toNative U ⋙ Over.forget _).prod' (degree U)

/-- Each time vertex remembers its entire graph lift over the original collapse. -/
abbrev family (P : Index U) (i : Fin (((degree U).obj P).len + 1)) :
    GraphLift U.left ((toNative U).obj P).left := (P.unop.snd i).val

theorem family_collapse (P : Index U) (i : Fin (((degree U).obj P).len + 1)) :
    (family U P i).collapse = ((toNative U).obj P).hom := (P.unop.snd i).property

/-- A joint operator simultaneously restricts the native source and the time family. -/
theorem family_map {P P' : Index U} (f : P ⟶ P') (i : Fin (((degree U).obj P).len + 1)) :
    family U P i = restrict (family U P' (((degree U).map f).toOrderHom i))
      ((toNative U).map f).left :=
  (congrArg Subtype.val (congrFun f.unop.property i)).symm

/-- The simultaneous resolution projects weakly onto the original native slice. -/
theorem toNative_weak : WeakEquivalence (nerveMap (toNative U)) := by
  let F := GrothendieckTotalElements.elementDiagram (timeDiagram U)
  let H := CategoryOfElements.π (G U) ⋙ CategoryTheory.Prod.fst _ _
  let e := GrothendieckTotalElements.equivalence (timeDiagram U)
  haveI : WeakEquivalence (nerveMap e.functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  haveI : WeakEquivalence (nerveMap (Grothendieck.forget F)) :=
    GrothendieckContractibleFibers.projection_weak F (fun P ↦ elements_point_GW U P.unop)
  have h : WeakEquivalence (nerveMap H) := by
    apply (weakEquivalence_precomp_iff (nerveMap e.functor) _).mp
    change WeakEquivalence (nerveMap (GrothendieckTotalElements.toTotal (timeDiagram U) ⋙
      CategoryOfElements.π (G U) ⋙ CategoryTheory.Prod.fst _ _))
    rw [GrothendieckTotalElements.forget_square (timeDiagram U)]
    infer_instance
  haveI : WeakEquivalence (nerveMap H.op) :=
    (TotalElementsWeakComparison.nerveMap_op_iff _).mpr h
  haveI : WeakEquivalence (nerveMap (unopUnop (NativeSlice U))) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  change WeakEquivalence (nerveMap H.op ≫ nerveMap (unopUnop (NativeSlice U)))
  infer_instance

/-- All actual internal necklaces in all the original variable-source cylinders. -/
abbrev Resolution := Grothendieck (joint U ⋙ JTGraphCylinderFiberDiagram.diagram)

/-- Every prescribed native collapse occurs with its original source necklace
in the time-zero cylinder. -/
def atZero (P : NativeSlice U) (D : Lifts U P.hom) : Resolution U where
  base := op ⟨(op P, op ⦋0⦌), fun _ ↦ D⟩
  fiber := JTGraphInterpolatedComparison.sliceObject P.left ⦋0⦌ 0

theorem atZero_native (P : NativeSlice U) (D : Lifts U P.hom) :
    (toNative U).obj (atZero U P D).base = P := rfl

/-- Forgetting time parameters and internal cylinder necklaces is Kan weak. -/
theorem resolution_toNative_weak : WeakEquivalence
    (nerveMap
      (Grothendieck.forget (joint U ⋙ JTGraphCylinderFiberDiagram.diagram) ⋙ toNative U)) := by
  let F := joint U ⋙ JTGraphCylinderFiberDiagram.diagram
  haveI : WeakEquivalence (nerveMap (Grothendieck.forget F)) :=
    GrothendieckContractibleFibers.projection_weak F (fun a ↦
      JTHomotopyTargetComma.fiber_point_GW_at ((joint U).obj a).1 ((joint U).obj a).2)
  haveI := toNative_weak U
  change WeakEquivalence (nerveMap (Grothendieck.forget F) ≫ nerveMap (toNative U))
  infer_instance

/-- The entire variable-source cylinder resolution is weakly contractible. -/
theorem resolution_point_GW : GW (pointMap (nerve (Resolution U))) := by
  let p := nerveMap (Grothendieck.forget (joint U ⋙ JTGraphCylinderFiberDiagram.diagram) ⋙
    toNative U)
  haveI : WeakEquivalence p := resolution_toNative_weak U
  haveI : WeakEquivalence (pointMap (nerve (NativeSlice U))) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeOverNerveWeakContractibility.point_GW U.left.fiber.left)
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (p ≫ pointMap (nerve (NativeSlice U)))
    (pointMap (nerve (Resolution U)))]
  infer_instance

end
end DaggerModels.PartII.JTGraphVariableTimeIndex
