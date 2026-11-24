import DaggerModelsPartII.ReducedCylinderColimits
import DaggerModelsPartII.JTXiAugmentation
import DaggerModelsPartII.JTXiOrdinaryLatching
import DaggerModelsPartII.ReedyFibrantDiagrams
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import TopCatModelCategory.ModelCategorySSet

/-!
# Relative Reedy cofibrancy of the literal collapsed Xi frame

The reduced cylinder in the undercategory gives the relative matching
condition. The natural comparison to the actual Xi coefficient retains the
original ordered boundary.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
  DaggerModels
open scoped SSet.modelCategoryQuillen
open OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTXiRelativeReedyFrame

open JTXiEndpointCollapse JTXiCoefficientEndpointIso JTXiAugmentation
open JTRelativeReedyFrame JTParameterLatchingMono
open JTEndpointObjects (Bdagger)

noncomputable section

private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{0}ᵒᵖ

/-- The native matching map of the actual parameter is the opposite of its
proper-face latching monomorphism, including in degree zero. -/
private theorem parameter_op_isFibrant : IsFibrant GroupoidSimplex.parameter.op := by
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  apply ((fibrations SSet.{0}ᵒᵖ).cancel_right_of_respectsIso
    ((matchingComparison n).app GroupoidSimplex.parameter.op)
    (JTXiOrdinaryLatching.parameterMatchingIso n).hom).mp
  rw [JTXiOrdinaryLatching.parameterMatchingIso_comp, fibrations_op]
  letI : Mono (faceLatchingMap n) := faceLatchingMap_mono n
  exact (cofibration_iff _).mp
    ((SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance)

private def j : boundary ⟶ interval := (SSet.boundary 1).ι
private local instance : Mono j := by
  change Mono (SSet.boundary 1).ι
  infer_instance

private def R : SSet.{0} ⥤ Under boundary := ReducedCylinder.functor j

private local instance : PreservesColimitsOfSize.{0,0} R := by
  dsimp [R]
  infer_instance

private local instance : ModelCategory (Under boundary) :=
  JTEndpointCobase.underModel boundary
private local instance : ModelCategory (Under boundary)ᵒᵖ := inferInstance
private local instance : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ (Under boundary)ᵒᵖ) :=
  simplicialReedyModelCategory (Under boundary)ᵒᵖ

private local instance : PreservesLimitsOfSize.{0,0} R.op := by
  exact preservesLimitsOfSize_op R

private theorem R_op_preservesFibrations {X Y : SSet.{0}ᵒᵖ}
    (f : X ⟶ Y) (hf : fibrations SSet.{0}ᵒᵖ f) :
    fibrations (Under boundary)ᵒᵖ (R.op.map f) := by
  rw [fibrations_op] at hf ⊢
  change cofibrations SSet.{0} f.unop at hf
  change cofibrations SSet.{0} ((R.map f.unop).right)
  letI : Mono f.unop := (SSet.modelCategoryQuillen.cofibration_iff f.unop).mp
    ((cofibration_iff f.unop).mpr hf)
  exact (cofibration_iff _).mp
    ((SSet.modelCategoryQuillen.cofibration_iff _).mpr
      (ReducedCylinder.map_mono j f.unop))

/-- The reduced cylinder of the actual parameter is relatively Reedy
cofibrant under the literal simplicial boundary. -/
private theorem reducedParameter_op_isFibrant :
    IsFibrant (GroupoidSimplex.parameter ⋙ R).op := by
  letI : IsFibrant GroupoidSimplex.parameter.op := parameter_op_isFibrant
  change IsFibrant (GroupoidSimplex.parameter.op ⋙ R.op)
  exact reedyFibrant_comp GroupoidSimplex.parameter.op R.op
    (fun f hf ↦ R_op_preservesFibrations f hf)

/-- Precomposition by the actual completed-simplex parameter; it preserves
pushouts because functor-category colimits are pointwise. -/
private def H : (SSet.{0} ⥤ SSet.{0}) ⥤ (SimplexCategory ⥤ SSet.{0}) :=
  (Functor.whiskeringLeft SimplexCategory SSet.{0} SSet.{0}).obj
    GroupoidSimplex.parameter

private local instance : PreservesColimitsOfSize.{0,0} H := by
  dsimp [H]
  infer_instance

private def ceValueIso :
    GroupoidSimplex.parameter ⋙ ReducedCylinder.value j ≅ CE := by
  change H.obj (pushout (ReducedCylinder.tensorInclusion j)
      (ReducedCylinder.tensorProjection boundary)) ≅
    pushout (H.map (ReducedCylinder.tensorInclusion j))
      (H.map (ReducedCylinder.tensorProjection boundary))
  exact (PreservesPushout.iso H (ReducedCylinder.tensorInclusion j)
    (ReducedCylinder.tensorProjection boundary)).symm

private def reducedBoundary :
    (Functor.const SimplexCategory).obj boundary ⟶
      GroupoidSimplex.parameter ⋙ ReducedCylinder.value j :=
  Functor.whiskerLeft GroupoidSimplex.parameter (ReducedCylinder.boundary j)

private theorem ceValueIso_boundary :
    reducedBoundary ≫ ceValueIso.hom = CE_boundary := by
  change H.map (pushout.inr (ReducedCylinder.tensorInclusion j)
      (ReducedCylinder.tensorProjection boundary)) ≫
        (PreservesPushout.iso H (ReducedCylinder.tensorInclusion j)
          (ReducedCylinder.tensorProjection boundary)).inv =
    pushout.inr (H.map (ReducedCylinder.tensorInclusion j))
      (H.map (ReducedCylinder.tensorProjection boundary))
  exact PreservesPushout.inr_iso_inv H
    (ReducedCylinder.tensorInclusion j)
    (ReducedCylinder.tensorProjection boundary)

/-- The parameterwise reduced cylinder is the actual CE pushout, with the
specified boundary map, naturally in the ordinary simplex index. -/
private def ceUnderIso :
    GroupoidSimplex.parameter ⋙ R ≅ Under.lift CE CE_boundary :=
  NatIso.ofComponents
    (fun k ↦ Under.isoMk (ceValueIso.app k)
      (NatTrans.congr_app ceValueIso_boundary k))
    (by
      intro k l f
      apply Under.UnderMorphism.ext
      exact ceValueIso.hom.naturality f)

private theorem ceUnder_op_isFibrant :
    IsFibrant (Under.lift CE CE_boundary).op := by
  letI : IsFibrant (GroupoidSimplex.parameter ⋙ R).op :=
    reducedParameter_op_isFibrant
  let e := NatIso.op ceUnderIso
  haveI : Fibration e.hom := inferInstance
  exact isFibrant_of_fibration e.hom

/-- The actual composite of the two original left adjoints. -/
private def F : SSet.{0} ⥤ Coefficient := freeDagger ⋙ daggerRigidification

private def U : Under boundary ⥤ Under Bdagger := Under.post F

private local instance : F.IsLeftAdjoint := by
  dsimp [F]
  letI : freeDagger.IsLeftAdjoint := freeDaggerAdjunction.isLeftAdjoint
  letI : daggerRigidification.IsLeftAdjoint :=
    DaggerActualRigidificationQuillen.adjunction.isLeftAdjoint
  infer_instance

private local instance : PreservesLimitsOfSize.{0,0} U.op := by
  let a := freeDaggerAdjunction.comp DaggerActualRigidificationQuillen.adjunction
  haveI : U.IsLeftAdjoint := by
    change (Under.post F).IsLeftAdjoint
    exact (Under.postAdjunctionLeft (X := boundary) a).isLeftAdjoint
  haveI : PreservesColimitsOfSize.{0,0} U := inferInstance
  exact preservesLimitsOfSize_op U

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory (Under Bdagger) :=
  JTEndpointCobase.underModel Bdagger
private local instance : ModelCategory (Under Bdagger)ᵒᵖ := inferInstance
private local instance : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ) :=
  simplicialReedyModelCategory (Under Bdagger)ᵒᵖ

private theorem U_op_preservesFibrations {X Y : (Under boundary)ᵒᵖ}
    (f : X ⟶ Y) (hf : fibrations (Under boundary)ᵒᵖ f) :
    fibrations (Under Bdagger)ᵒᵖ (U.op.map f) := by
  rw [fibrations_op] at hf ⊢
  change cofibrations SSet.{0} f.unop.right at hf
  change cofibrations Coefficient (F.map f.unop.right)
  letI : Mono f.unop.right :=
    (SSet.modelCategoryQuillen.cofibration_iff f.unop.right).mp
      ((cofibration_iff f.unop.right).mpr hf)
  have hFree : Cofibration (freeDagger.map f.unop.right) := by
    apply (cofibration_iff _).mpr
    rw [DaggerActualRigidificationQuillen.source_cof]
    exact freeDagger_map_isFreeCofibration f.unop.right
  letI : daggerRigidification.PreservesCofibrations :=
    DaggerActualRigidificationQuillen.preservesCofibrations
  letI : Cofibration (freeDagger.map f.unop.right) := hFree
  exact (cofibration_iff _).mp (inferInstance :
    Cofibration (daggerRigidification.map (freeDagger.map f.unop.right)))

private theorem mappedCE_op_isFibrant :
    IsFibrant ((Under.lift CE CE_boundary ⋙ U).op) := by
  letI : IsFibrant (Under.lift CE CE_boundary).op :=
    ceUnder_op_isFibrant
  change IsFibrant ((Under.lift CE CE_boundary).op ⋙ U.op)
  exact reedyFibrant_comp (Under.lift CE CE_boundary).op U.op
    (fun f hf ↦ U_op_preservesFibrations f hf)

/-- The checked strict coefficient iso transports the *ordered boundary*,
not merely the underlying collapsed coefficient diagram. -/
private theorem coefficientRawCE_boundary :
    coefficientBoundary ≫ coefficientRawCEIso.hom =
      (Functor.constComp SimplexCategory boundary F).inv ≫
        Functor.whiskerRight CE_boundary F := by
  apply NatTrans.ext
  funext k
  have hRaw : coefficientBoundary.app k ≫
      JTXiEndpointRigidification.coefficientToRaw.app k =
      JTXiEndpointRigidification.rawRigidifiedBoundary.app k := by
    simpa only [coefficientBoundary, NatTrans.comp_app] using
      NatTrans.congr_app
        JTXiEndpointRigidification.boundary_coefficientToRaw k
  have hFree : rawBoundary.app k ≫
      JTXiStrictEndpointIso.rawXiCollapseIso.hom.app k =
      CEFreeBoundary.app k := by
    exact NatTrans.congr_app
      JTXiStrictEndpointIso.rawBoundary_rawXiCollapseIso k
  change ((coefficientBoundary.app k ≫
      JTXiEndpointRigidification.coefficientToRaw.app k) ≫
      daggerRigidification.map (JTXiStrictEndpointIso.rawXiCollapseIso.hom.app k)) = _
  rw [hRaw]
  change daggerRigidification.map
      (JTXiEndpointCollapse.rawBoundary.app k) ≫
      daggerRigidification.map (JTXiStrictEndpointIso.rawXiCollapseIso.hom.app k) = _
  rw [← Functor.map_comp, hFree]
  rfl

/-- The actual Xi coefficient cobase is the mapped CE reduced cylinder as an
object of the original undercategory. -/
private def actualXiUnderIso : XiFrame ≅ Under.lift CE CE_boundary ⋙ U :=
  NatIso.ofComponents
    (fun k ↦ Under.isoMk (coefficientRawCEIso.app k)
      (NatTrans.congr_app coefficientRawCE_boundary k))
    (by
      intro k l f
      apply Under.UnderMorphism.ext
      exact coefficientRawCEIso.hom.naturality f)

/-- Relative Reedy cofibrancy of the literal endpoint-collapsed Xi frame,
including the original ordered degree-zero boundary. -/
theorem XiFrame_op_isFibrant : IsFibrant XiFrame.op := by
  letI : IsFibrant ((Under.lift CE CE_boundary ⋙ U).op) :=
    mappedCE_op_isFibrant
  let e := NatIso.op actualXiUnderIso
  haveI : Fibration e.inv := inferInstance
  exact isFibrant_of_fibration e.inv

end

end DaggerModels.PartII.JTXiRelativeReedyFrame
