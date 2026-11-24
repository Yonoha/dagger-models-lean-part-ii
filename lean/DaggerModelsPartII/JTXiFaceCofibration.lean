import DaggerModelsPartII.FreeDaggerFixedSimplex
import DaggerModelsPartII.JTXiTwoCopyFrame
import DaggerModelsPartII.JTXiRawSeamPushout
import DaggerModelsPartII.JTXiEndpointRigidification
import NativeMonoRestrictionParameterizedWalkingLifting

/-!
# Free cofibration of the actual Xi endpoint face map

The two-copy presentation makes the raw face map monic.  A fixed simplex
in the target has its first coordinate in the common vertex image, so it
already comes from the ordered boundary cylinder and hence from the raw
face source.  This proves the original free-cofibration predicate without
altering the endpoint span or the parameter.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory DaggerModels
open HomotopicalAlgebra OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTXiFaceCofibration

open JTXiEndpointCollapse JTXiEndpointCollapseBoundary
open JTXiTwoCopyFrame JTXiRawSeamPushout JTRelativeReedyFrame
open JTCEVertices GroupoidSimplex GroupoidSimplexReversal

noncomputable section

private theorem inl_mono : Mono (FreeDaggerPushout.inl interval) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  exact (mono_iff_injective _).2 (FreeDaggerPushout.inl_app_injective interval q)

private theorem cylinderInclusion_mono (k : SimplexCategory) :
    Mono (cylinderInclusion.app k) := by
  letI : Mono (SSet.boundary 1).ι := inferInstance
  change Mono ((SSet.boundary 1).ι ▷ parameter.obj k)
  exact DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono
    (SSet.boundary 1).ι (parameter.obj k)

/-- The original raw endpoint-face map is monic after forgetting. -/
theorem rawFaces_hom_mono (k : SimplexCategory) :
    Mono (DaggerSSet.forget.map (rawFaces.app k)) := by
  let F := frameOneUnderlyingIso k
  let e := seamSourceIso k
  letI : Mono (FreeDaggerPushout.inl interval) := inl_mono
  letI : Mono (FreeDaggerPushout.inl interval ▷ parameter.obj k) :=
    DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono
      (FreeDaggerPushout.inl interval) (parameter.obj k)
  letI : Mono (cylinderInclusion.app k) := cylinderInclusion_mono k
  have hcomparison : Mono
      ((cylinderInclusion.app k ≫ forwardFrame.app k) ≫ F.hom) := by
    rw [Category.assoc, forwardFrame_calibration]
    infer_instance
  have hforward : Mono (cylinderInclusion.app k ≫ forwardFrame.app k) := by
    letI : Mono ((cylinderInclusion.app k ≫ forwardFrame.app k) ≫ F.hom) :=
      hcomparison
    haveI : Mono
        (((cylinderInclusion.app k ≫ forwardFrame.app k) ≫ F.hom) ≫ F.inv) :=
      inferInstance
    have hcancel :
        ((cylinderInclusion.app k ≫ forwardFrame.app k) ≫ F.hom) ≫ F.inv =
          cylinderInclusion.app k ≫ forwardFrame.app k := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hcancel] at this
    exact this
  have hsource : Mono
      (e.hom ≫ DaggerSSet.forget.map (rawFaces.app k)) := by
    rw [seamSourceIso_faces]
    exact hforward
  letI : Mono (e.hom ≫ DaggerSSet.forget.map (rawFaces.app k)) := hsource
  haveI : Mono
      (e.inv ≫ (e.hom ≫ DaggerSSet.forget.map (rawFaces.app k))) :=
    inferInstance
  have hcancel : e.inv ≫
      (e.hom ≫ DaggerSSet.forget.map (rawFaces.app k)) =
        DaggerSSet.forget.map (rawFaces.app k) := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hcancel] at this
  exact this

private theorem boundary_vertex_lift :
    JTCEVertices.boundaryAsVertices.inv ≫ (SSet.boundary 1).ι =
      SSetVertices.inclusion interval := by
  rw [← JTCEVertices.boundaryAsVertices_inclusion,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

set_option maxRecDepth 100000 in
/-- Every dagger-fixed simplex of the actual degree-one frame is in the
image of the original raw face map, in every simplex degree. -/
theorem fixed_mem_rawFaces (k : SimplexCategory) (n : ℕ)
    (x : (frame1.obj k).toSSet _⦋n⦌)
    (hfix : (frame1.obj k).daggerSimplex x = x) :
    x ∈ Set.range ((rawFaces.app k).hom.app (op ⦋n⦌)) := by
  let F := frameOneUnderlyingIso k
  obtain ⟨v, ξ, hv⟩ :=
    FreeDaggerFixedSimplex.tensor_fixed_mem_vertices interval
      (frame1.obj k) (daggerParameter.obj k) F
      (frameOne_dagger k) n x hfix
  let w : (boundaryCylinder.obj k).obj (op ⦋n⦌) :=
    ((JTCEVertices.boundaryAsVertices.inv).app (op ⦋n⦌) v, ξ)
  have hb := congrFun
    (NatTrans.congr_app boundary_vertex_lift (op ⦋n⦌)) v
  have hw : (cylinderInclusion.app k).app (op ⦋n⦌) w =
      ((SSetVertices.inclusion interval).app (op ⦋n⦌) v, ξ) := by
    apply Prod.ext
    · exact hb
    · rfl
  have hf := congrFun
    (NatTrans.congr_app (forwardFrame_calibration k) (op ⦋n⦌))
      ((SSetVertices.inclusion interval).app (op ⦋n⦌) v, ξ)
  have hs := congrFun
    (NatTrans.congr_app (seamSourceIso_faces k) (op ⦋n⦌)) w
  refine ⟨(seamSourceIso k).hom.app (op ⦋n⦌) w, ?_⟩
  apply (mono_iff_injective (F.hom.app (op ⦋n⦌))).1 inferInstance
  calc
    F.hom.app (op ⦋n⦌)
        ((rawFaces.app k).hom.app (op ⦋n⦌)
          ((seamSourceIso k).hom.app (op ⦋n⦌) w)) =
      F.hom.app (op ⦋n⦌)
        ((forwardFrame.app k).app (op ⦋n⦌)
          ((cylinderInclusion.app k).app (op ⦋n⦌) w)) := by
        exact congrArg (F.hom.app (op ⦋n⦌)) hs
    _ = ((SSetVertices.inclusion interval ≫ FreeDaggerPushout.inl interval).app
          (op ⦋n⦌) v, ξ) := by
        rw [hw]
        simpa only [NatTrans.comp_app, types_comp_apply] using hf
    _ = F.hom.app (op ⦋n⦌) x := hv.symm

/-- The actual ordered Xi endpoint face map is a free cofibration. -/
theorem rawFaces_freeCofibration (k : SimplexCategory) :
    DaggerSSet.FreeCofibration (rawFaces.app k) := by
  refine ⟨(DaggerSSet.mono_iff_mono_hom (rawFaces.app k)).2
      (rawFaces_hom_mono k), ?_⟩
  intro n hn x hx hnew hfix
  exact hnew (fixed_mem_rawFaces k n x hfix)

section Coefficient

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : HasLimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasLimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : daggerRigidification.{0}.PreservesCofibrations :=
  DaggerActualRigidificationQuillen.preservesCofibrations

/-- The original rigidified Xi endpoint face map is a cofibration in
the existing dagger simplicial-category model structure. -/
theorem endpointFaces_isCofibration (k : SimplexCategory) :
    Cofibration ((JTEndpointHom.endpointFaces XiCurried).app k) := by
  haveI : Cofibration (rawFaces.app k) := by
    apply (cofibration_iff _).2
    rw [DaggerActualRigidificationQuillen.source_cof]
    exact rawFaces_freeCofibration k
  haveI : Cofibration (daggerRigidification.map (rawFaces.app k)) :=
    inferInstance
  rw [← JTXiEndpointRigidification.sourceComparison_faces k]
  infer_instance

/-- The predicate form used by the original coefficient-frame arguments. -/
theorem endpointFaces_cof (k : SimplexCategory) :
    cofibrations Coefficient
      ((JTEndpointHom.endpointFaces XiCurried).app k) :=
  (cofibration_iff _).1 (endpointFaces_isCofibration k)

end Coefficient

end

end DaggerModels.PartII.JTXiFaceCofibration
