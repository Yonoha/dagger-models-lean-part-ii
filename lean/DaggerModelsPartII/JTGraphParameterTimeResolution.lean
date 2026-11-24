import DaggerModelsPartII.JTHomotopyTargetTimeResolution
import DaggerModelsPartII.JTGraphInterpolatedComparison
import DaggerModelsPartII.JTGraphMultiBeadIdentityLift
import DaggerModelsPartII.JTGraphInterpolatedOverTime
import NativeOverNerveWeakContractibility

/-! All interpolated graph parameters over a prescribed original collapse. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphParameterTimeResolution

open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport JTGraphInterpolatedRaw JTGraphInterpolatedComparison
open JTProjectiveOrderedFiberComparison (row)
open JTHomotopyTargetTimeResolution JTNecklaceEndpointCylinder
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open DaggerOriginalCodiscreteNerveInjective (codiscreteNerve)
open JTGraphInterpolatedCollapseOriginal
  (indexCollapse indexCollapse_operator pullbackLift pullback_collapse timeCollapse)
open JTTargetCommaPullback (diagram toPullback equivalence)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q) {S : NecklaceCode} (c : S ⟶ U.left.fiber.left)

/-- The exact graph parameters whose collapse is the prescribed native arrow. -/
abbrev Lifts := {D : GraphLift U.left S // D.collapse = c}

/-- All ordered time families, with restriction along every simplex operator. -/
def timeSpace : SSet.{0} where
  obj n := Fin (n.unop.len + 1) → Lifts U c
  map j t := t ∘ j.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

private def timeIso : timeSpace U c ≅ codiscreteNerve.obj (Lifts U c) :=
  NatIso.ofComponents
    (fun n ↦ (Equiv.mk Codiscrete.functor (fun F i ↦ (F.obj i).as) (fun _ ↦ rfl)
      (fun _ ↦ nerve.ext_of_isThin (by funext i; rfl))).toIso)
    (by intros; rfl)

/-- If the specified collapse has one graph lift, the entire resolution of
all of its time families and original internal necklaces is weakly contractible. -/
theorem resolution_point_GW (D : Lifts U c) :
    GW (pointMap (nerve (TimeResolution S (timeSpace U c)))) := by
  have : Nonempty (Lifts U c) := ⟨D⟩
  let t := pointMap (codiscreteNerve.obj (Lifts U c))
  have ht := DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration t pointIsTerminal
  have : WeakEquivalence t := ((mem_trivialFibrations_iff _).mp ht).2
  have h : (timeIso U c).hom ≫ t = pointMap (timeSpace U c) := pointIsTerminal.hom_ext _ _
  apply (point_GW_iff S (timeSpace U c)).mpr
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

private abbrev Idx := (timeSpace U c).Elementsᵒᵖ
private abbrev deg (P : Idx U c) := P.unop.fst.unop
private abbrev family (P : Idx U c) (i : Fin ((deg U c P).len + 1)) :=
  (P.unop.snd i).val
private theorem family_collapse (P : Idx U c) (i : Fin ((deg U c P).len + 1)) :
    (family U c P i).collapse = c := (P.unop.snd i).property

private abbrev k := index U c
private abbrev Sourced := degree (timeSpace U c) ⋙ under S
private abbrev Dest := (JTTargetCommaPullback.diagram W x y Q).obj (k U c)

private def decorated (P : Idx U c) :
    (Sourced U c).obj P ⟶ (underDiagram W x y).obj (k U c) :=
  toDecorated U c (fun i ↦ (family U c P i).parameter)

private theorem whole (P : Idx U c) :
    (decorated U c P).right ≫ ((underCocone W x y).app (k U c)).right =
      NecklaceCylinderAugmentation.augmentation S (deg U c P) ≫ (c ≫ U.hom.hom).map ≫ Q.map := by
  apply whole_raw
  intro i
  have h := (family U c P i).comm
  rw [family_collapse U c P i] at h
  exact h

private theorem decorated_natural {P P' : Idx U c} (f : P ⟶ P') :
    (Sourced U c).map f ≫ decorated U c P' = decorated U c P := by
  let j : deg U c P ⟶ deg U c P' := (degree (timeSpace U c)).map f
  have h : (fun i ↦ family U c P' (j.toOrderHom i)) = family U c P := by
    funext i
    exact congrArg Subtype.val (congrFun f.unop.property i)
  change (under S).map j ≫ decorated U c P' = _
  exact (decorated_reindex c (family U c P') j).trans
    (congrArg (toDecorated U c)
      (congrArg (fun F : Fin ((deg U c P).len + 1) → GraphLift U.left S ↦
        fun i ↦ (F i).parameter) h))

set_option maxHeartbeats 600000 in
/-- The comparisons for all graph parameter families assemble over the
entire native time resolution and retain the original target arrow. -/
def liftNatural : Sourced U c ⟶ (Functor.const _).obj (Dest U c) where
  app P := pullbackLift (U := U) (n := deg U c P) c (family U c P) (family_collapse U c P)
  naturality {P P'} f := by
    let j : deg U c P ⟶ deg U c P' := (degree (timeSpace U c)).map f
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact JTCylinderOverTargetReindex.lift_reindex W x y Q (k U c) S (deg U c P)
      (deg U c P') j (decorated U c P) (decorated U c P') (c ≫ U.hom.hom)
      (whole U c P) (whole U c P') (decorated_natural U c f)

/-- The full time resolution of graph predecessors maps into the original comma. -/
def toComma : TimeResolution S (timeSpace U c) ⥤ TargetComma Q :=
  BoundaryNecklaceComma.toTarget (Sourced U c) (liftNatural U c) ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (JTTargetCommaPullback.diagram W x y Q))
      (k U c) ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse

private def collapseNatural :
    Sourced U c ⟶ (Functor.const _).obj
      (BoundaryNecklaceComma.necklaceUnder.obj U.left.fiber.left) where
  app P := timeCollapse (n := deg U c P) c
  naturality {P P'} f := by
    change (under S).map ((degree (timeSpace U c)).map f) ≫
      timeCollapse (n := deg U c P') c = timeCollapse (n := deg U c P) c ≫ 𝟙 _
    rw [Category.comp_id]
    exact JTGraphInterpolatedOverTime.timeCollapse_reindex c
      ((degree (timeSpace U c)).map f)

private def indexToOriginal :
    (Functor.const (Idx U c)).obj (k U c) ⟶ (Functor.const (Idx U c)).obj U.left.base where
  app P := indexCollapse (U := U) (n := deg U c P) c (family U c P) (family_collapse U c P)
  naturality {P P'} _ := by
    change 𝟙 (k U c) ≫ indexCollapse c (family U c P') (family_collapse U c P') =
      indexCollapse c (family U c P) (family_collapse U c P) ≫ 𝟙 U.left.base
    rw [Category.id_comp, Category.comp_id]
    have hP := indexCollapse_operator (U := U) (n := deg U c P) c
      (family U c P) (family_collapse U c P)
    have hP' := indexCollapse_operator (U := U) (n := deg U c P') c
      (family U c P') (family_collapse U c P')
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg (fun f ↦ f.op) (hP'.trans hP.symm)

private theorem lift_app (P : Idx U c) : (liftNatural U c).app P =
    pullbackLift (U := U) (n := deg U c P) c (family U c P) (family_collapse U c P) := rfl

private theorem index_app (P : Idx U c) : (indexToOriginal U c).app P =
    indexCollapse (U := U) (n := deg U c P) c (family U c P) (family_collapse U c P) := rfl

private theorem native_app (P : Idx U c) : (collapseNatural U c).app P =
    timeCollapse (n := deg U c P) c := rfl

private theorem collapse_square (P : Idx U c) :
    (liftNatural U c).app P ≫ (diagram W x y Q).map ((indexToOriginal U c).app P) =
      (collapseNatural U c).app P ≫ ((toPullback W x y Q).obj U).fiber.hom := by
  rw [lift_app, index_app, native_app]
  exact pullback_collapse (U := U) (n := deg U c P) c (family U c P) (family_collapse U c P)

/-- Every time and internal-necklace operator in the full graph resolution
commutes with the collapse to the same original comma object. -/
def comparisonToOriginal :
    toComma U c ⟶ (Functor.const (TimeResolution S (timeSpace U c))).obj U :=
  JTBoundaryNecklaceConeReindex.mapCone
    (JTBoundaryNecklacePresentationCone.coneFromDiagram (diagram W x y Q)
      ((toPullback W x y Q).obj U) (Sourced U c) (liftNatural U c)
      (indexToOriginal U c) (collapseNatural U c) (collapse_square U c))
    (equivalence W x y Q).inverse ((equivalence W x y Q).unitIso.app U).inv

/-- The full graph resolution is a functor into the actual slice over the
original comma object, with the same underlying comparison. -/
def toSlice : TimeResolution S (timeSpace U c) ⥤ Over U :=
  Over.lift (toComma U c) (comparisonToOriginal U c)

theorem toSlice_forget : toSlice U c ⋙ Over.forget U = toComma U c := rfl

/-- The comparison into the original slice is a weak equivalence on nerves. -/
theorem toSlice_weak (D : Lifts U c) :
    WeakEquivalence (nerveMap (toSlice U c)) := by
  let p := pointMap (nerve (Over U))
  have : WeakEquivalence p := (weakEquivalence_iff_GW _).mpr
    (DaggerNativeOverNerveWeakContractibility.point_GW U)
  apply (weakEquivalence_postcomp_iff (nerveMap (toSlice U c)) p).mp
  rw [pointIsTerminal.hom_ext (nerveMap (toSlice U c) ≫ p) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mpr (resolution_point_GW U c D)

/-- Every original comma object has a weakly contractible time resolution
of its identity-collapse graph parameters, for arbitrary native target. -/
theorem identity_resolution_point_GW :
    GW (pointMap (nerve (TimeResolution U.left.fiber.left (timeSpace U (𝟙 _))))) := by
  obtain ⟨D, hD⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift U.left
  exact resolution_point_GW U (𝟙 _) ⟨D, hD⟩

/-- Every original comma object has a weak comparison into its actual slice. -/
theorem identity_toSlice_weak : WeakEquivalence (nerveMap (toSlice U (𝟙 _))) := by
  obtain ⟨D, hD⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift U.left
  exact toSlice_weak U (𝟙 _) ⟨D, hD⟩

end

end DaggerModels.PartII.JTGraphParameterTimeResolution
