import DaggerModelsPartII.JTXiEndpointCollapse
import DaggerModelsPartII.JTEndpointHom
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# The original rigidified Xi endpoint cobase

Rigidification and evaluation preserve the actual raw pushout and its two
endpoint coproducts. The resulting comparison identifies the literal B-first
coefficient cobase with rigidification of the original raw dagger pushout.
Both actual coprojections are calibrated. This does not assert the remaining
raw Xi/free-CE isomorphism or derived endpoint-fiber weakness.
-/

set_option autoImplicit false
open CategoryTheory Limits Simplicial DaggerModels
open OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTXiEndpointRigidification

open JTXiEndpointCollapse JTRelativeReedyFrame JTActualCosimplicialFrame

noncomputable section

private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : HasLimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasLimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : HomotopicalAlgebra.ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : PreservesColimits daggerRigidification.{0} :=
  DaggerActualRigidificationQuillen.adjunction.leftAdjoint_preservesColimits

/-- Evaluation followed by the original dagger rigidification. -/
def coefficientEvaluation (k : SimplexCategory) :
    (SimplexCategory ⥤ DaggerSSet.{0}) ⥤ DaggerSimplicialCat.{0, 0} :=
  (evaluation SimplexCategory DaggerSSet.{0}).obj k ⋙ daggerRigidification

private local instance (k : SimplexCategory) :
    PreservesColimitsOfSize.{0, 0} (coefficientEvaluation k) := by
  dsimp only [coefficientEvaluation]
  infer_instance

/-- The native coproduct comparison from the actual two coefficient frames. -/
def sourceComparison (k : SimplexCategory) :
    (JTEndpointHom.endpointSource XiCurried).obj k ⟶
      daggerRigidification.obj ((frame0 ⨿ frame0).obj k) :=
  coprodComparison (coefficientEvaluation k) frame0 frame0

instance sourceComparison_isIso (k : SimplexCategory) : IsIso (sourceComparison k) := by
  change IsIso (coprodComparison (coefficientEvaluation k) frame0 frame0)
  infer_instance

private theorem sourceComparison_inl (k : SimplexCategory) :
    (coprod.inl : (XiCurried.obj k).obj JTZeroObjects.zeroIndex ⟶
      (JTEndpointHom.endpointSource XiCurried).obj k) ≫ sourceComparison k =
      daggerRigidification.map ((coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k) :=
  coprodComparison_inl (coefficientEvaluation k) (A := frame0) (B := frame0)

private theorem sourceComparison_inr (k : SimplexCategory) :
    (coprod.inr : (XiCurried.obj k).obj JTZeroObjects.zeroIndex ⟶
      (JTEndpointHom.endpointSource XiCurried).obj k) ≫ sourceComparison k =
      daggerRigidification.map ((coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k) :=
  coprodComparison_inr (coefficientEvaluation k) (A := frame0) (B := frame0)

/-- The comparison respects both original ordered frame cofaces. -/
theorem sourceComparison_faces (k : SimplexCategory) :
    sourceComparison k ≫ daggerRigidification.map (rawFaces.app k) =
      (JTEndpointHom.endpointFaces XiCurried).app k := by
  apply coprod.hom_ext
  · rw [← Category.assoc, sourceComparison_inl]
    change daggerRigidification.map ((coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k) ≫
        daggerRigidification.map (rawFaces.app k) = _
    rw [← Functor.map_comp, ← NatTrans.comp_app]
    simp only [rawFaces, coprod.inl_desc, JTEndpointHom.endpointFaces]
    rfl
  · rw [← Category.assoc, sourceComparison_inr]
    change daggerRigidification.map ((coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k) ≫
        daggerRigidification.map (rawFaces.app k) = _
    rw [← Functor.map_comp, ← NatTrans.comp_app]
    simp only [rawFaces, coprod.inr_desc, JTEndpointHom.endpointFaces]
    rfl

/-- The original Xi augmentation gives exactly the rigidified raw collapse. -/
theorem sourceComparison_endpoints (k : SimplexCategory) :
    sourceComparison k ≫ daggerRigidification.map (rawEndpoints.app k) =
      (JTEndpointHom.endpointCollapse XiAugmentationCurried).app k := by
  apply coprod.hom_ext
  · rw [← Category.assoc, sourceComparison_inl]
    change daggerRigidification.map ((coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k) ≫
        daggerRigidification.map (rawEndpoints.app k) = _
    rw [← Functor.map_comp, ← NatTrans.comp_app]
    simp only [rawEndpoints, coprod.inl_desc, JTEndpointHom.endpointCollapse]
    change daggerRigidification.map
        ((frame0Projection.app k) ≫ freeDagger.map (boundaryVertexMap 0)) = _
    simp only [frame0Projection, Functor.map_comp]
    rfl
  · rw [← Category.assoc, sourceComparison_inr]
    change daggerRigidification.map ((coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k) ≫
        daggerRigidification.map (rawEndpoints.app k) = _
    rw [← Functor.map_comp, ← NatTrans.comp_app]
    simp only [rawEndpoints, coprod.inr_desc, JTEndpointHom.endpointCollapse]
    change daggerRigidification.map
        ((frame0Projection.app k) ≫ freeDagger.map (boundaryVertexMap 1)) = _
    simp only [frame0Projection, Functor.map_comp]
    rfl

/-- The original rigidification of the actual raw endpoint-collapse diagram. -/
def rawRigidified : SimplexCategory ⥤ DaggerSimplicialCat.{0, 0} :=
  rawCollapse ⋙ daggerRigidification

/-- The literal rigidified frame coprojection. -/
def rawRigidifiedFrame :
    XiCurried ⋙ (evaluation ReverseSimplex Coefficient).obj JTOrderedFrameMate.oneIndex ⟶
      rawRigidified where
  app k := daggerRigidification.map ((pushout.inl rawFaces rawEndpoints).app k)
  naturality {k l} θ := by
    change daggerRigidification.map (frame1.map θ) ≫ _ =
      _ ≫ daggerRigidification.map (rawCollapse.map θ)
    simpa only [Functor.map_comp] using
      congrArg daggerRigidification.map ((pushout.inl rawFaces rawEndpoints).naturality θ)

/-- The literal rigidified boundary coprojection with the constant-base normalization. -/
def rawRigidifiedBoundary :
    (Functor.const SimplexCategory).obj JTEndpointObjects.Bdagger ⟶ rawRigidified where
  app k := daggerRigidification.map (rawBoundary.app k)
  naturality {k l} θ := by
    change 𝟙 _ ≫ _ = _ ≫ daggerRigidification.map (rawCollapse.map θ)
    rw [Category.id_comp]
    have h := rawBoundary.naturality θ
    change 𝟙 B ≫ rawBoundary.app l = rawBoundary.app k ≫ rawCollapse.map θ at h
    rw [Category.id_comp] at h
    simpa only [daggerRigidification.map_comp] using congrArg daggerRigidification.map h

/-- The mapped raw pushout is precisely the original coefficient endpoint span. -/
theorem rawRigidified_isPushout (k : SimplexCategory) :
    IsPushout ((JTEndpointHom.endpointFaces XiCurried).app k)
      ((JTEndpointHom.endpointCollapse XiAugmentationCurried).app k)
      (rawRigidifiedFrame.app k) (rawRigidifiedBoundary.app k) := by
  have h := (IsPushout.of_hasPushout rawFaces rawEndpoints).map (coefficientEvaluation k)
  apply h.of_iso' (asIso (sourceComparison k)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using sourceComparison_faces k
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using
      sourceComparison_endpoints k
  · rfl
  · rfl

private theorem rawRigidified_condition :
    JTEndpointHom.endpointCollapse XiAugmentationCurried ≫ rawRigidifiedBoundary =
      JTEndpointHom.endpointFaces XiCurried ≫ rawRigidifiedFrame := by
  apply NatTrans.ext
  funext k
  exact (rawRigidified_isPushout k).w.symm

/-- The actual coefficient endpoint cobase maps to the rigidified raw pushout. -/
def coefficientToRaw :
    JTEndpointHom.collapsedFrame XiAugmentationCurried ⟶ rawRigidified :=
  pushout.desc rawRigidifiedBoundary rawRigidifiedFrame rawRigidified_condition

/-- This comparison preserves the actual fixed boundary coprojection. -/
theorem boundary_coefficientToRaw :
    JTEndpointCobase.endpointCobase_inl (JTEndpointHom.endpointFaces XiCurried)
        JTEndpointObjects.Bdagger (JTEndpointHom.endpointCollapse XiAugmentationCurried) ≫
      coefficientToRaw = rawRigidifiedBoundary := by
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inl_desc _ _ _

/-- This comparison preserves the actual outer-one frame coprojection. -/
theorem frame_coefficientToRaw :
    JTEndpointCobase.endpointCobase_inr (JTEndpointHom.endpointFaces XiCurried)
        JTEndpointObjects.Bdagger (JTEndpointHom.endpointCollapse XiAugmentationCurried) ≫
      coefficientToRaw = rawRigidifiedFrame := by
  change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inr_desc _ _ _

private def componentIso (k : SimplexCategory) :
    (JTEndpointHom.collapsedFrame XiAugmentationCurried).obj k ≅ rawRigidified.obj k :=
  (JTEndpointCobase.endpointCobase_isPushout_at (JTEndpointHom.endpointFaces XiCurried)
    JTEndpointObjects.Bdagger (JTEndpointHom.endpointCollapse XiAugmentationCurried) k).isoIsPushout
      _ _ (rawRigidified_isPushout k).flip

private theorem coefficientToRaw_app_eq (k : SimplexCategory) :
    coefficientToRaw.app k = (componentIso k).hom := by
  apply (JTEndpointCobase.endpointCobase_isPushout_at (JTEndpointHom.endpointFaces XiCurried)
    JTEndpointObjects.Bdagger (JTEndpointHom.endpointCollapse XiAugmentationCurried) k).hom_ext
  · simpa only [NatTrans.comp_app, componentIso, IsPushout.inl_isoIsPushout_hom] using
      NatTrans.congr_app boundary_coefficientToRaw k
  · simpa only [NatTrans.comp_app, componentIso, IsPushout.inr_isoIsPushout_hom] using
      NatTrans.congr_app frame_coefficientToRaw k

instance coefficientToRaw_isIso : IsIso coefficientToRaw := by
  letI (k : SimplexCategory) : IsIso (coefficientToRaw.app k) := by
    rw [coefficientToRaw_app_eq]
    infer_instance
  exact NatIso.isIso_of_isIso_app coefficientToRaw

/-- The calibrated original coefficient endpoint cobase is the rigidified raw pushout. -/
def coefficientRawIso :
    JTEndpointHom.collapsedFrame XiAugmentationCurried ≅ rawRigidified :=
  asIso coefficientToRaw

end

end DaggerModels.PartII.JTXiEndpointRigidification
