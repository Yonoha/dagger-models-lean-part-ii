import DaggerModelsPartII.JTCEVertices
import DaggerModelsPartII.JTParameterReversal

/-!
# The reversed endpoint-collapse pushout and its literal vertex seam

Reversal fixes the discrete ordered boundary. The reverse interval cylinder
still carries the actual groupoid parameter inversion. Transporting the
ordinary CE pushout through these isomorphisms gives its reverse-copy
pushout over that same boundary. The free dagger CE pushout is calibrated
to this literal seam rather than a different vertex object.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTCEReversalPushout

open JTXiEndpointCollapse JTCEVertices GroupoidSimplex GroupoidSimplexReversal

noncomputable section

private local instance : SSet.opFunctor.IsEquivalence :=
  show SSet.opEquivalence.functor.IsEquivalence by infer_instance

/-- Reversal of the literal discrete two-vertex boundary, fixing its vertices. -/
def boundaryReversalIso : boundary ≅ boundary.op :=
  boundaryVerticesIso.symm ≪≫ SSetVertices.opIso boundary ≪≫
    SSet.opFunctor.mapIso boundaryVerticesIso

/-- A map out of the discrete boundary is reversed through its actual
vertex map. No reversal of the ordered boundary vertices is inserted. -/
theorem boundaryReversal_map {X : SSet.{0}} (f : boundary ⟶ X) :
    boundaryReversalIso.hom ≫ SSet.opFunctor.map f =
      boundaryVerticesIso.inv ≫ SSetVertices.map f ≫ SSetVertices.opInclusion X := by
  apply (cancel_epi boundaryVerticesIso.hom).1
  simp only [boundaryReversalIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change (SSetVertices.opIso boundary).hom ≫
      SSet.opFunctor.map (SSetVertices.inclusion boundary) ≫ SSet.opFunctor.map f =
    SSetVertices.map f ≫ SSetVertices.opInclusion X
  rw [← Category.assoc, SSetVertices.opIso_hom_op_inclusion]
  exact (SSetVertices.map_opInclusion f).symm

/-- The actual reversed endpoint inclusion into the interval. -/
theorem boundaryReversal_interval :
    boundaryReversalIso.hom ≫ SSet.opFunctor.map (SSet.boundary 1).ι =
      boundaryAsVertices.hom ≫ SSetVertices.opInclusion interval := by
  rw [boundaryReversal_map]
  rfl

/-- The actual reversed endpoint inclusion into CE, with its calibrated seam. -/
theorem boundaryReversal_CE (k : SimplexCategory) :
    boundaryReversalIso.hom ≫ SSet.opFunctor.map (CE_boundary.app k) =
      (ceVerticesIso k).inv ≫ SSetVertices.opInclusion (CE.obj k) := by
  rw [boundaryReversal_map]
  rfl

/-- The reverse boundary cylinder still has the unchanged J factor. -/
def reverseCylinderInclusion (k : SimplexCategory) :
    boundaryCylinder.obj k ⟶ interval.op ⊗ parameter.obj k :=
  (boundaryAsVertices.hom ≫ SSetVertices.opInclusion interval) ▷ parameter.obj k

/-- The reverse interval cylinder is sent to CE.op using the actual J dagger. -/
def reverseCEInterval (k : SimplexCategory) :
    interval.op ⊗ parameter.obj k ⟶ (CE.obj k).op :=
  (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
    SSet.opFunctor.map (CE_interval.app k)

/-- The prescribed reversed inclusion of the same ordered boundary. -/
def reverseCEBoundary (k : SimplexCategory) : boundary ⟶ (CE.obj k).op :=
  boundaryReversalIso.hom ≫ SSet.opFunctor.map (CE_boundary.app k)

/-- The original forward CE pushout evaluated at the literal parameter k. -/
theorem forward_isPushout (k : SimplexCategory) :
    IsPushout (cylinderInclusion.app k) (cylinderProjection.app k)
      (CE_interval.app k) (CE_boundary.app k) :=
  (IsPushout.of_hasPushout cylinderInclusion cylinderProjection).map
    ((evaluation SimplexCategory SSet.{0}).obj k)

/-- Reversing CE uses the literal boundary and the actual groupoid inversion. -/
theorem reverse_isPushout (k : SimplexCategory) :
    IsPushout (reverseCylinderInclusion k) (cylinderProjection.app k)
      (reverseCEInterval k) (reverseCEBoundary k) := by
  let eS : boundaryCylinder.obj k ≅ (boundaryCylinder.obj k).op :=
    tensorIso boundaryReversalIso (daggerParameter.obj k).daggerIso
  let eA : interval.op ⊗ parameter.obj k ≅ (intervalCylinder.obj k).op :=
    tensorIso (Iso.refl interval.op) (daggerParameter.obj k).daggerIso
  apply ((forward_isPushout k).map SSet.opFunctor).of_iso'
    eS eA boundaryReversalIso (Iso.refl _)
  · change (boundaryReversalIso.hom ⊗ₘ (daggerParameter.obj k).dagger) ≫
        (SSet.opFunctor.map (SSet.boundary 1).ι ⊗ₘ 𝟙 _) =
      ((boundaryAsVertices.hom ≫ SSetVertices.opInclusion interval) ⊗ₘ 𝟙 _) ≫
        (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger)
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [boundaryReversal_interval]
  · change (boundaryReversalIso.hom ⊗ₘ (daggerParameter.obj k).dagger) ≫
        CartesianMonoidalCategory.fst boundary.op (parameter.obj k).op =
      CartesianMonoidalCategory.fst boundary (parameter.obj k) ≫ boundaryReversalIso.hom
    exact CartesianMonoidalCategory.tensorHom_fst _ _
  · change (𝟙 interval.op ⊗ₘ (daggerParameter.obj k).dagger) ≫
      SSet.opFunctor.map (CE_interval.app k) = reverseCEInterval k ≫ 𝟙 _
    exact (Category.comp_id _).symm
  · change boundaryReversalIso.hom ≫ SSet.opFunctor.map (CE_boundary.app k) =
      reverseCEBoundary k ≫ 𝟙 _
    exact (Category.comp_id _).symm

/-- The explicit free dagger CE pushout uses this same ordered boundary
for its seam after the actual CE vertex identification. -/
theorem free_isPushout (k : SimplexCategory) :
    IsPushout (CE_boundary.app k) (reverseCEBoundary k)
      (FreeDaggerPushout.inl (CE.obj k)) (FreeDaggerPushout.inr (CE.obj k)) := by
  apply (IsPushout.of_hasPushout (SSetVertices.inclusion (CE.obj k))
    (SSetVertices.opInclusion (CE.obj k))).of_iso
      (ceVerticesIso k) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Category.comp_id] using (ceVerticesIso_inclusion k).symm
  · change SSetVertices.opInclusion (CE.obj k) ≫ 𝟙 _ =
      (ceVerticesIso k).hom ≫ reverseCEBoundary k
    rw [Category.comp_id]
    unfold reverseCEBoundary
    rw [boundaryReversal_CE, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · simp [FreeDaggerPushout.inl]
  · simp [FreeDaggerPushout.inr]

end

end DaggerModels.PartII.JTCEReversalPushout
