import DaggerModelsPartII.JTEndpointObjects
import DaggerModelsPartII.JTEndpointHom
import DaggerModelsPartII.ResolutionGeneratorCofibrancy
import DaggerModels.FreeDaggerCofibration

/-!
# Cofibrancy of the original ordered endpoint arrow at degree zero

The original free dagger boundary and interval are rigidified using the
unchanged Quillen adjunction. The two object classifiers supply the canonical
boundary coproduct. The actual zero Xi endpoint arrow is conjugate to the
original rigidified free boundary inclusion, with its ordered faces fixed.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels
open OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTEndpointCofibrancy

open JTZeroObjects JTEndpointObjects JTOrderedFrameMate
open RigidifiedJTFrames JTRelativeReedyFrame

noncomputable section

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
private local instance : PreservesColimits daggerRigidification.{0} :=
  DaggerActualRigidificationQuillen.adjunction.leftAdjoint_preservesColimits

/-- The original rigidified free dagger interval. -/
def Jdagger : DaggerSimplicialCat.{0, 0} :=
  daggerRigidification.obj (freeDagger.obj (Δ[1] : SSet.{0}))

/-- The literal original ordered boundary inclusion. -/
def iota : Bdagger ⟶ Jdagger :=
  daggerRigidification.map (freeDagger.map (SSet.boundary 1).ι)

/-- The actual boundary is cofibrant because it is rigidification of a free object. -/
theorem boundary_isCofibrant : IsCofibrant Bdagger := by
  letI : IsCofibrant B := freeDagger_isCofibrant boundary
  change IsCofibrant (daggerRigidification.obj B)
  apply (isCofibrant_iff_of_isInitial
    (daggerRigidification.map (initial.to B))
    (initialIsInitial.isInitialObj daggerRigidification _)).mpr
  infer_instance

/-- The actual ordered inclusion is a cofibration in the original dagger model. -/
theorem iota_isCofibration : Cofibration iota := by
  have : Cofibration (freeDagger.map (SSet.boundary 1).ι) := by
    apply (cofibration_iff _).2
    rw [DaggerActualRigidificationQuillen.source_cof]
    exact freeDagger_map_isFreeCofibration _
  change Cofibration (daggerRigidification.map (freeDagger.map (SSet.boundary 1).ι))
  infer_instance

private def boundaryDesc {C : DaggerSimplicialCat.{0, 0}}
    (f g : A.obj zeroIndex ⟶ C) : Bdagger ⟶ C :=
  (boundaryPairEquiv C).symm (zeroHomEquiv C f, zeroHomEquiv C g)

private theorem endpoint_zero_boundaryDesc {C : DaggerSimplicialCat.{0, 0}}
    (f g : A.obj zeroIndex ⟶ C) : endpointMap 0 ≫ boundaryDesc f g = f := by
  apply (zeroHomEquiv C).injective
  have h := (boundaryPairEquiv C).apply_symm_apply (zeroHomEquiv C f, zeroHomEquiv C g)
  rw [boundaryPairEquiv_apply] at h
  exact congrArg Prod.fst h

private theorem endpoint_one_boundaryDesc {C : DaggerSimplicialCat.{0, 0}}
    (f g : A.obj zeroIndex ⟶ C) : endpointMap 1 ≫ boundaryDesc f g = g := by
  apply (zeroHomEquiv C).injective
  have h := (boundaryPairEquiv C).apply_symm_apply (zeroHomEquiv C f, zeroHomEquiv C g)
  rw [boundaryPairEquiv_apply] at h
  exact congrArg Prod.snd h

private theorem boundary_hom_ext {C : DaggerSimplicialCat.{0, 0}}
    {f g : Bdagger ⟶ C} (h0 : endpointMap 0 ≫ f = endpointMap 0 ≫ g)
    (h1 : endpointMap 1 ≫ f = endpointMap 1 ≫ g) : f = g := by
  apply (boundaryPairEquiv C).injective
  rw [boundaryPairEquiv_apply, boundaryPairEquiv_apply]
  exact Prod.ext (congrArg (zeroHomEquiv C) h0) (congrArg (zeroHomEquiv C) h1)

/-- The canonical two-zero-frame coproduct is the literal original boundary. -/
def endpointCoproductIso : A.obj zeroIndex ⨿ A.obj zeroIndex ≅ Bdagger where
  hom := coprod.desc (endpointMap 0) (endpointMap 1)
  inv := boundaryDesc coprod.inl coprod.inr
  hom_inv_id := by
    apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc, endpoint_zero_boundaryDesc, Category.comp_id]
    · simp only [coprod.inr_desc_assoc, endpoint_one_boundaryDesc, Category.comp_id]
  inv_hom_id := by
    apply boundary_hom_ext
    · rw [← Category.assoc, endpoint_zero_boundaryDesc, coprod.inl_desc, Category.comp_id]
    · rw [← Category.assoc, endpoint_one_boundaryDesc, coprod.inr_desc, Category.comp_id]

/-- Normalize the source of the actual Xi endpoint arrow in degree zero. -/
def sourceZeroIso :
    (JTEndpointHom.endpointSource XiCurried).obj ⦋0⦌ ≅ Bdagger :=
  coprod.mapIso (XiZeroIso.app zeroIndex) (XiZeroIso.app zeroIndex) ≪≫
    endpointCoproductIso

/-- Normalize the target of the same actual degree-zero arrow. -/
def targetZeroIso :
    (XiCurried.obj ⦋0⦌).obj oneIndex ≅ Jdagger :=
  XiZeroIso.app oneIndex ≪≫
    daggerRigidification.mapIso (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋1⦌)

private theorem boundaryVertexMap_inclusion (i : Fin 2) :
    boundaryVertexMap i ≫ (SSet.boundary 1).ι =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) := by
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, boundaryVertexMap, Equiv.apply_symm_apply]
  rfl

private theorem endpoint_iota (i : Fin 2) :
    A.map (vertex i) ≫
        daggerRigidification.map
          (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋1⦌).hom =
      endpointMap i ≫ iota := by
  have h := DaggerJTFrameUnderlying.reversalSimplexFreeIso.hom.naturality
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)
  change DaggerJTFrameUnderlying.reversalSimplex.map (vertex i) ≫
      (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋1⦌).hom =
    (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋0⦌).hom ≫
      freeDagger.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)) at h
  rw [← boundaryVertexMap_inclusion i, freeDagger.map_comp] at h
  simpa only [Functor.comp_map, A, endpointMap, zeroInputIso, iota,
    Functor.mapIso_hom, daggerRigidification.map_comp, Category.assoc] using
      congrArg daggerRigidification.map h

private theorem zeroFace_component (i : Fin 2) :
    (XiCurried.obj ⦋0⦌).map (vertex i) ≫ targetZeroIso.hom =
      (XiZeroIso.app zeroIndex).hom ≫ endpointMap i ≫ iota := by
  have h := XiZeroIso.hom.naturality (vertex i)
  change (XiCurried.obj ⦋0⦌).map (vertex i) ≫ (XiZeroIso.app oneIndex).hom =
    (XiZeroIso.app zeroIndex).hom ≫ A.map (vertex i) at h
  change _ ≫ ((XiZeroIso.app oneIndex).hom ≫ _) = _
  rw [← Category.assoc, h, Category.assoc]
  change _ ≫ (A.map (vertex i) ≫ daggerRigidification.map
    (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋1⦌).hom) = _
  rw [endpoint_iota]

/-- The actual degree-zero face square is the original ordered inclusion. -/
theorem zeroFace_square :
    (JTEndpointHom.endpointFaces XiCurried).app ⦋0⦌ ≫ targetZeroIso.hom =
      sourceZeroIso.hom ≫ iota := by
  apply coprod.hom_ext
  · simpa only [JTEndpointHom.endpointFaces, coprod.inl_desc_assoc, sourceZeroIso,
      Iso.trans_hom, coprod.mapIso_hom, coprod.inl_map_assoc, endpointCoproductIso,
      coprod.inl_desc_assoc, Category.assoc] using zeroFace_component 0
  · simpa only [JTEndpointHom.endpointFaces, coprod.inr_desc_assoc, sourceZeroIso,
      Iso.trans_hom, coprod.mapIso_hom, coprod.inr_map_assoc, endpointCoproductIso,
      coprod.inr_desc_assoc, Category.assoc] using zeroFace_component 1

/-- The literal zero Xi endpoint arrow is isomorphic to the original iota. -/
def zeroArrowIso :
    Arrow.mk ((JTEndpointHom.endpointFaces XiCurried).app ⦋0⦌) ≅ Arrow.mk iota :=
  Arrow.isoMk sourceZeroIso targetZeroIso zeroFace_square.symm

/-- The source of the actual zero Xi endpoint arrow is cofibrant. -/
theorem source_zero_isCofibrant :
    IsCofibrant ((JTEndpointHom.endpointSource XiCurried).obj ⦋0⦌) := by
  have : IsCofibrant Bdagger := boundary_isCofibrant
  exact isCofibrant_of_cofibration sourceZeroIso.inv

/-- The actual zero Xi endpoint face arrow is a cofibration. -/
theorem zeroFace_isCofibration :
    Cofibration ((JTEndpointHom.endpointFaces XiCurried).app ⦋0⦌) := by
  apply (cofibration_iff _).2
  exact ((cofibrations DaggerSimplicialCat.{0, 0}).arrow_mk_iso_iff zeroArrowIso).2
    ((cofibration_iff iota).1 iota_isCofibration)

end

end DaggerModels.PartII.JTEndpointCofibrancy
