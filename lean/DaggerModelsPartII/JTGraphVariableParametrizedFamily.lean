import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTGraphVariableTimeTraversal
import NativeOverNerveWeakContractibility

/-! The existing variable-source graph resolution is an actual coherent parameter family. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphVariableParametrizedFamily

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableTimeIndex (Index toNative family family_map family_collapse toNative_weak)
open JTGraphVariableTimeTraversal (labels)
open JTGraphLiftTransport (GraphLift)
open JTParametrizedTargetFamilies (Family)
open JTGraphParameterInterpolation (interpolate)
open JTInterpolatedCylinderReindex (interpolate_reindex)
open JTInterpolatedCylinderSource (interpolate_source)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q)

private abbrev time := JTGraphVariableTimeIndex.degree U
private abbrev obj (P : Index U) := (toNative U).obj P
private abbrev T (P : Index U) := (obj U P).left
private abbrev param (P : Index U) (i : Fin (((time U).obj P).len + 1)) :=
  (family U P i).parameter

private theorem parameter_map {P P' : Index U} (f : P ⟶ P') :
    (((toNative U).map f).left.map ⊗ₘ J.map ((time U).map f)) ≫ interpolate (param U P') =
      interpolate (param U P) := by
  let g := ((toNative U).map f).left
  let j := (time U).map f
  have h : param U P = fun i ↦ g.map ≫ param U P' (j.toOrderHom i) := by
    funext i
    exact congrArg GraphLift.parameter (family_map U f i)
  calc
    _ = (g.map ⊗ₘ 𝟙 (J.obj ((time U).obj P))) ≫
          (𝟙 (T U P').toSSet ⊗ₘ J.map j) ≫ interpolate (param U P') := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    _ = _ := by rw [interpolate_reindex, interpolate_source, ← h]

set_option maxHeartbeats 650000 in
/-- Reuse every original graph parameter simplex, including its changing
native source, as a coherent family over the unchanged raw target. -/
def coherentFamily : Family Q (labels U) (time U) where
  collapse :=
    { app P := (obj U P).hom ≫ U.hom.hom
      naturality {P P'} f := by
        change ((toNative U).map f).left ≫ ((obj U P').hom ≫ U.hom.hom) =
          ((obj U P).hom ≫ U.hom.hom) ≫ 𝟙 _
        rw [← Category.assoc, Over.w ((toNative U).map f), Category.comp_id] }
  parameter P := interpolate (param U P)
  parameter_map {P P'} f := by
    change (((toNative U).map f).left.map ⊗ₘ J.map ((time U).map f)) ≫
      interpolate (param U P') = interpolate (param U P) ≫ J.map (𝟙 _)
    rw [J.map_id, Category.comp_id]
    exact parameter_map U f
  raw P := by
    exact JTGraphInterpolatedRaw.whole_raw U (obj U P).hom (param U P) (fun i ↦ by
      have h := (family U P i).comm
      rw [family_collapse U P i] at h
      exact h)

/-- The original graph-parameter index is weakly contractible before adding
all the internal necklaces. -/
theorem index_point_GW : GW (pointMap (nerve (Index U))) := by
  let P := toNative U
  letI : WeakEquivalence (nerveMap P) := toNative_weak U
  letI : WeakEquivalence (pointMap (nerve (JTGraphVariableTimeIndex.NativeSlice U))) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeOverNerveWeakContractibility.point_GW U.left.fiber.left)
  have h : nerveMap P ≫ pointMap (nerve (JTGraphVariableTimeIndex.NativeSlice U)) =
    pointMap (nerve (Index U)) := pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end

end DaggerModels.PartII.JTGraphVariableParametrizedFamily
