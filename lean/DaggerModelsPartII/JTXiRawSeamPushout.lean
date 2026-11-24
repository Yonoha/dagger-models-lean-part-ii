import DaggerModelsPartII.JTXiEndpointCollapseBoundary
import DaggerModelsPartII.JTCEVertices
import DaggerModelsPartII.JTWalkingUnitaryWeak
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The underlying raw endpoint pushout at an arbitrary parameter

The raw dagger pushout is evaluated and forgotten, then its source and
boundary are identified with the two ordered summands of the ordinary
boundary cylinder. The two endpoint equations calibrate the literal span.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTXiRawSeamPushout

open JTXiEndpointCollapse JTXiEndpointCollapseBoundary
open DaggerJTFrameUnderlying JTCEVertices GroupoidSimplex

noncomputable section

private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits

/-- The literal boundary unit is invertible because the one-boundary is
already its discrete simplicial set of vertices. -/
private theorem boundaryUnit_isIso :
    IsIso (freeDaggerAdjunction.unit.app boundary) := by
  haveI : IsIso (SSetVertices.inclusion boundary) := by
    change IsIso boundaryVerticesIso.hom
    infer_instance
  haveI : IsIso (SSetVertices.opInclusion boundary) := by
    rw [← SSetVertices.opIso_hom_op_inclusion]
    infer_instance
  haveI : IsIso (FreeDaggerPushout.inl boundary) :=
    (IsPushout.of_hasPushout (SSetVertices.inclusion boundary)
      (SSetVertices.opInclusion boundary)).isIso_inl_of_isIso
  rw [← FreeDaggerPushout.inl_isoFreeDagger_hom]
  infer_instance

/-- The actual chosen unit, rather than an arbitrary boundary equivalence. -/
def boundaryUnitIso : boundary ≅ B.toSSet := by
  letI : IsIso (freeDaggerAdjunction.unit.app boundary) :=
    boundaryUnit_isIso
  exact asIso (freeDaggerAdjunction.unit.app boundary)

private def zeroFrameUnderlyingIsTerminal :
    IsTerminal (underlyingSimplex.obj m0) := by
  letI : PreservesLimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesLimits
  have h : IsTerminal ((freeDagger.obj (Δ[0] : SSet.{0})).toSSet) :=
    JTWalkingUnitaryWeak.freeZeroIsTerminal.isTerminalObj
      DaggerSSet.forget _
  exact IsTerminal.ofIso h
    (DaggerSSet.forget.mapIso (reversalSimplexFreeIso.app ⦋0⦌)).symm

private theorem forwardSimplex_zero_isIso :
    IsIso (forwardSimplexNat.app ⦋0⦌) :=
  isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀
    zeroFrameUnderlyingIsTerminal _

/-- The actual first-copy map at horizontal degree zero is an isomorphism
at every parameter, including the full groupoid parameter. -/
private theorem forwardFrame0_isIso (k : SimplexCategory) :
    IsIso (forwardFrame0.app k) := by
  letI : IsIso (forwardSimplexNat.app ⦋0⦌) :=
    forwardSimplex_zero_isIso
  haveI : IsIso (forwardParameter0.app k) := by
    change IsIso
      ((forwardSimplexNat.app ⦋0⦌) ⊗ₘ (𝟙 (parameter.obj k)))
    infer_instance
  dsimp only [forwardFrame0, NatTrans.comp_app]
  infer_instance

/-- `∂Δ[1] × J[k]` is the coproduct of the two actual point cylinders,
with the native ordered vertex inclusions. -/
private def boundaryCylinderCoproductIso (k : SimplexCategory) :
    boundaryCylinder.obj k ≅ zeroCylinder.obj k ⨿ zeroCylinder.obj k := by
  change (boundary ⊗ parameter.obj k) ≅
    ((Δ[0] : SSet.{0}) ⊗ parameter.obj k) ⨿
      ((Δ[0] : SSet.{0}) ⊗ parameter.obj k)
  exact IsColimit.coconePointUniqueUpToIso
    (SSet.boundary₁.isColimitRightTensor (parameter.obj k))
    (colimit.isColimit (pair
      ((Δ[0] : SSet.{0}) ⊗ parameter.obj k)
      ((Δ[0] : SSet.{0}) ⊗ parameter.obj k)))

/-- The source of the forgotten raw span is the literal boundary cylinder.
The first factor uses the native binary-coproduct presentation of `∂Δ[1]`;
the last two factors use preservation by dagger forgetting and evaluation. -/
def seamSourceIso (k : SimplexCategory) :
    boundaryCylinder.obj k ≅
      DaggerSSet.forget.obj ((frame0 ⨿ frame0).obj k) := by
  letI : IsIso (forwardFrame0.app k) := forwardFrame0_isIso k
  letI : PreservesColimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesColimits
  let e := PreservesColimitPair.iso
    ((evaluation SimplexCategory DaggerSSet.{0}).obj k) frame0 frame0
  exact boundaryCylinderCoproductIso k ≪≫
    coprod.mapIso (asIso (forwardFrame0.app k))
      (asIso (forwardFrame0.app k)) ≪≫
    PreservesColimitPair.iso DaggerSSet.forget
      (frame0.obj k) (frame0.obj k) ≪≫
    DaggerSSet.forget.mapIso e

private theorem seamSourceIso_inl (k : SimplexCategory) :
    (SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫ (seamSourceIso k).hom =
      forwardFrame0.app k ≫ DaggerSSet.forget.map
        ((coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (SSet.boundary₁.isColimitRightTensor (parameter.obj k))
    (colimit.isColimit (pair
      ((Δ[0] : SSet.{0}) ⊗ parameter.obj k)
      ((Δ[0] : SSet.{0}) ⊗ parameter.obj k))) (.mk .left)
  have h' : (SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫
      (boundaryCylinderCoproductIso k).hom = coprod.inl := by
    simpa only [BinaryCofan.ι_app_left, BinaryCofan.mk_inl,
      colimit.cocone_ι] using h
  simp only [seamSourceIso, Iso.trans_hom]
  rw [← Category.assoc, h']
  simp only [coprod.mapIso_hom, PreservesColimitPair.iso_hom,
    Functor.mapIso_hom, asIso_hom,
    coprod.inl_map_assoc]
  change forwardFrame0.app k ≫ coprod.inl ≫
      coprodComparison DaggerSSet.forget (frame0.obj k) (frame0.obj k) ≫
        DaggerSSet.forget.map (coprodComparison
          ((evaluation SimplexCategory DaggerSSet.{0}).obj k) frame0 frame0) =
    forwardFrame0.app k ≫ DaggerSSet.forget.map
      ((coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k)
  rw [coprodComparison_inl_assoc, ← DaggerSSet.forget.map_comp]
  have hE := coprodComparison_inl ((evaluation SimplexCategory DaggerSSet.{0}).obj k)
    (A := frame0) (B := frame0)
  exact congrArg (fun q ↦ forwardFrame0.app k ≫ DaggerSSet.forget.map q) hE

private theorem seamSourceIso_inr (k : SimplexCategory) :
    (SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫ (seamSourceIso k).hom =
      forwardFrame0.app k ≫ DaggerSSet.forget.map
        ((coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (SSet.boundary₁.isColimitRightTensor (parameter.obj k))
    (colimit.isColimit (pair
      ((Δ[0] : SSet.{0}) ⊗ parameter.obj k)
      ((Δ[0] : SSet.{0}) ⊗ parameter.obj k))) (.mk .right)
  have h' : (SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫
      (boundaryCylinderCoproductIso k).hom = coprod.inr := by
    simpa only [BinaryCofan.ι_app_right, BinaryCofan.mk_inr,
      colimit.cocone_ι] using h
  simp only [seamSourceIso, Iso.trans_hom]
  rw [← Category.assoc, h']
  simp only [coprod.mapIso_hom, PreservesColimitPair.iso_hom,
    Functor.mapIso_hom, asIso_hom,
    coprod.inr_map_assoc]
  change forwardFrame0.app k ≫ coprod.inr ≫
      coprodComparison DaggerSSet.forget (frame0.obj k) (frame0.obj k) ≫
        DaggerSSet.forget.map (coprodComparison
          ((evaluation SimplexCategory DaggerSSet.{0}).obj k) frame0 frame0) =
    forwardFrame0.app k ≫ DaggerSSet.forget.map
      ((coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k)
  rw [coprodComparison_inr_assoc, ← DaggerSSet.forget.map_comp]
  have hE := coprodComparison_inr ((evaluation SimplexCategory DaggerSSet.{0}).obj k)
    (A := frame0) (B := frame0)
  exact congrArg (fun q ↦ forwardFrame0.app k ≫ DaggerSSet.forget.map q) hE

/-- The original raw dagger pushout remains a pushout after evaluation
and dagger forgetting; no arbitrary-colimit claim about a right adjoint
is used, since this particular forgetful functor preserves colimits. -/
private theorem forgottenRaw_isPushout (k : SimplexCategory) :
    IsPushout
      (DaggerSSet.forget.map (rawFaces.app k))
      (DaggerSSet.forget.map (rawEndpoints.app k))
      (DaggerSSet.forget.map ((pushout.inl rawFaces rawEndpoints).app k))
      (DaggerSSet.forget.map ((pushout.inr rawFaces rawEndpoints).app k)) := by
  letI : PreservesColimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesColimits
  have h := (IsPushout.of_hasPushout rawFaces rawEndpoints).map
    ((evaluation SimplexCategory DaggerSSet.{0}).obj k)
  exact h.map DaggerSSet.forget

/-- Calibration of the first span leg. The only required equality is on
the two native boundary-cylinder coprojections; these are exactly
`frameEndpointSquare 0` and `frameEndpointSquare 1`. -/
private theorem seam_face (k : SimplexCategory) :
    (seamSourceIso k).hom ≫ DaggerSSet.forget.map (rawFaces.app k) =
      cylinderInclusion.app k ≫ forwardFrame.app k := by
  apply SSet.boundary₁.hom_ext_rightTensor
  · rw [← Category.assoc]
    change ((SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫
      (seamSourceIso k).hom) ≫ DaggerSSet.forget.map (rawFaces.app k) = _
    rw [seamSourceIso_inl]
    change forwardFrame0.app k ≫
        DaggerSSet.forget.map ((coprod.inl ≫ rawFaces).app k) = _
    rw [rawFaces, coprod.inl_desc]
    exact (frameEndpointSquare 0 k).symm
  · rw [← Category.assoc]
    change ((SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫
      (seamSourceIso k).hom) ≫ DaggerSSet.forget.map (rawFaces.app k) = _
    rw [seamSourceIso_inr]
    change forwardFrame0.app k ≫
        DaggerSSet.forget.map ((coprod.inr ≫ rawFaces).app k) = _
    rw [rawFaces, coprod.inr_desc]
    exact (frameEndpointSquare 1 k).symm

/-- Calibration of the second span leg by the two ordered projection
relations `projectionEndpointSquare 0` and `projectionEndpointSquare 1`. -/
private theorem seam_boundary (k : SimplexCategory) :
    (seamSourceIso k).hom ≫ DaggerSSet.forget.map (rawEndpoints.app k) =
      cylinderProjection.app k ≫ (boundaryUnitIso).hom := by
  apply SSet.boundary₁.hom_ext_rightTensor
  · rw [← Category.assoc]
    change ((SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫
      (seamSourceIso k).hom) ≫ DaggerSSet.forget.map (rawEndpoints.app k) = _
    rw [seamSourceIso_inl]
    change forwardFrame0.app k ≫
        DaggerSSet.forget.map ((coprod.inl ≫ rawEndpoints).app k) = _
    rw [rawEndpoints, coprod.inl_desc]
    exact (projectionEndpointSquare 0 k).symm
  · rw [← Category.assoc]
    change ((SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫
      (seamSourceIso k).hom) ≫ DaggerSSet.forget.map (rawEndpoints.app k) = _
    rw [seamSourceIso_inr]
    change forwardFrame0.app k ≫
        DaggerSSet.forget.map ((coprod.inr ≫ rawEndpoints).app k) = _
    rw [rawEndpoints, coprod.inr_desc]
    exact (projectionEndpointSquare 1 k).symm

/-- The literal underlying raw collapse is the pushout of the common
seam into the degree-one frame and the original ordered boundary. -/
theorem rawSeam_isPushout (k : SimplexCategory) :
    IsPushout
      (cylinderInclusion.app k ≫ forwardFrame.app k)
      (cylinderProjection.app k)
      (DaggerSSet.forget.map ((pushout.inl rawFaces rawEndpoints).app k))
      (boundaryToRaw.app k) := by
  apply (forgottenRaw_isPushout k).of_iso'
    (seamSourceIso k) (Iso.refl _) boundaryUnitIso (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using seam_face k
  · exact seam_boundary k
  · simp
  · change boundaryUnitIso.hom ≫
        DaggerSSet.forget.map ((pushout.inr rawFaces rawEndpoints).app k) =
          boundaryToRaw.app k
    simp [boundaryUnitIso, boundaryToRaw, rawBoundary]
    cat_disch

/-- The existing source isomorphism preserves the literal ordered face span. -/
theorem seamSourceIso_faces (k : SimplexCategory) :
    (seamSourceIso k).hom ≫ DaggerSSet.forget.map (rawFaces.app k) =
      cylinderInclusion.app k ≫ forwardFrame.app k :=
  seam_face k

/-- The same source isomorphism preserves the original ordered endpoint collapse. -/
theorem seamSourceIso_endpoints (k : SimplexCategory) :
    (seamSourceIso k).hom ≫ DaggerSSet.forget.map (rawEndpoints.app k) =
      cylinderProjection.app k ≫ boundaryUnitIso.hom :=
  seam_boundary k

end

end DaggerModels.PartII.JTXiRawSeamPushout
