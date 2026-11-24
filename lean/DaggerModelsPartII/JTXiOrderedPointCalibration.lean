import DaggerModelsPartII.JTXiRowEndpoints
import DaggerModelsPartII.JTRightAdjointOrderedFiber
import DaggerModelsPartII.JTXiEndpointRigidification

/-! The literal Xi endpoint point is the ordered point of the original dagger row. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open OrdinaryRigidification
open OrdinaryRigidification.DaggerNerve OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTXiOrderedPointCalibration

open JTXiRowEndpoints JTEndpointHom JTEndpointObjects JTZeroObjects
open JTRelativeReedyFrame JTActualCosimplicialFrame JTRightAdjointOrderedFiber JTUnderlyingOrderedFibers

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

private theorem transpose_boundary (C : DaggerSimplicialCat.{0, 0})
    (x y : (daggerCoherentNerve.obj C).toSSet.obj (op ⦋0⦌)) :
    (DaggerActualRigidificationQuillen.adjunction.homEquiv B C).symm
        (daggerBoundary (daggerCoherentNerve.obj C) x y) =
      boundaryTarget C (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat x)
        (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat y) := by
  apply (boundaryPairEquiv C).injective
  rw [show boundaryPairEquiv C (boundaryTarget C _ _) = (_, _) from
    (boundaryPairEquiv C).apply_symm_apply _]
  have h (f : Bdagger ⟶ C) : DaggerAdjunction.homEquiv B C f =
      DaggerActualRigidificationQuillen.adjunction.homEquiv B C f := by
    apply DaggerSSet.Hom.ext
    exact (DaggerAdjunction.homEquiv_hom B C f).trans
      (daggerRigidificationLiftWitness.homEquiv_compatibility B C f)
  let f := (DaggerActualRigidificationQuillen.adjunction.homEquiv B C).symm
    (daggerBoundary (daggerCoherentNerve.obj C) x y)
  have hf : DaggerAdjunction.homEquiv B C f =
      daggerBoundary (daggerCoherentNerve.obj C) x y :=
    (h f).trans ((DaggerActualRigidificationQuillen.adjunction.homEquiv B C).apply_symm_apply _)
  let e := freeDaggerAdjunction.homEquiv boundary (daggerCoherentNerve.obj C)
  let v := Equiv.prodCongr (NerveVertices.vertexEquiv C.toSimplicialCat)
    (NerveVertices.vertexEquiv C.toSimplicialCat)
  let r := boundaryHomEquiv (daggerCoherentNerve.obj C).toSSet
  change v (r (e (DaggerAdjunction.homEquiv B C f))) = v (x, y)
  have hboundary : e (DaggerAdjunction.homEquiv B C f) = r.symm (x, y) :=
    (congrArg e hf).trans (daggerBoundary_transpose (daggerCoherentNerve.obj C) x y)
  exact congrArg v ((congrArg r hboundary).trans (r.apply_symm_apply (x, y)))

private theorem endpointCollapse_rigidified (k : SimplexCategory) (i : Fin 2) :
    daggerRigidification.map ((JTXiEndpointCollapse.endpointCollapse i).app k) =
      (XiAugmentationCurried.app k).app zeroIndex ≫ endpointMap i := by
  change daggerRigidification.map (JTXiEndpointCollapse.frame0Projection.app k ≫
      freeDagger.map (JTXiEndpointCollapse.boundaryVertexMap i)) = _
  simp only [JTXiEndpointCollapse.frame0Projection, Functor.map_comp]
  rfl

private theorem vertexPoint_calibration (C : DaggerSimplicialCat.{0, 0})
    (x y : (daggerCoherentNerve.obj C).toSSet.obj (op ⦋0⦌))
    (i : Fin 2) (k : SimplexCategory) (s : (Δ[0] : SSet.{0}).obj (op k)) :
    (xiRowMappingIso C zeroIndex).hom.app (op k)
        ((daggerVertexPoint (daggerCoherentNerve.obj C) x y i).app (op k) s) =
      (XiAugmentationCurried.app k).app zeroIndex ≫ endpointMap i ≫
        boundaryTarget C (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat x)
          (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat y) := by
  change (DaggerActualRigidificationQuillen.adjunction.homEquiv
      (DaggerJTAdjunction.frame.obj (zeroIndex, k)) C).symm
        ((JTXiEndpointCollapse.endpointCollapse i).app k ≫
          daggerBoundary (daggerCoherentNerve.obj C) x y) = _
  rw [DaggerActualRigidificationQuillen.adjunction.homEquiv_naturality_left_symm,
    endpointCollapse_rigidified]
  have ht := transpose_boundary C x y
  exact (congrArg (fun z ↦ ((XiAugmentationCurried.app k).app zeroIndex ≫ endpointMap i) ≫ z)
    ht).trans (Category.assoc _ _ _)

/-- The actual categorical product point agrees with the literal ordered
nerve point defined by the same coefficient objects. -/
theorem daggerEndpointPoint_eq_boundaryPoint (C : DaggerSimplicialCat.{0, 0})
    (x y : (daggerCoherentNerve.obj C).toSSet.obj (op ⦋0⦌)) :
    daggerEndpointPoint (daggerCoherentNerve.obj C) x y =
      boundaryPoint C (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat x)
        (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat y) := by
  apply (cancel_mono ((xiCategoricalPairIso C).hom ≫ (xiZeroPairIso C).hom)).mp
  rw [boundaryPoint_square]
  have hp : daggerEndpointPoint (daggerCoherentNerve.obj C) x y ≫
      (xiCategoricalPairIso C).hom =
      FunctorToTypes.prod.lift (daggerVertexPoint (daggerCoherentNerve.obj C) x y 0)
        (daggerVertexPoint (daggerCoherentNerve.obj C) x y 1) := by
    have h₀ : (daggerEndpointPoint (daggerCoherentNerve.obj C) x y ≫
        (xiCategoricalPairIso C).hom) ≫ FunctorToTypes.prod.fst =
        daggerVertexPoint (daggerCoherentNerve.obj C) x y 0 := by
      rw [Category.assoc, xiCategoricalPairIso, FunctorToTypes.binaryProductIso_hom_comp_fst,
        daggerEndpointPoint]
      exact Limits.prod.lift_fst _ _
    have h₁ : (daggerEndpointPoint (daggerCoherentNerve.obj C) x y ≫
        (xiCategoricalPairIso C).hom) ≫ FunctorToTypes.prod.snd =
        daggerVertexPoint (daggerCoherentNerve.obj C) x y 1 := by
      rw [Category.assoc, xiCategoricalPairIso, FunctorToTypes.binaryProductIso_hom_comp_snd,
        daggerEndpointPoint]
      exact Limits.prod.lift_snd _ _
    apply NatTrans.ext
    funext k s
    exact Prod.ext (congrFun (NatTrans.congr_app h₀ k) s)
      (congrFun (NatTrans.congr_app h₁ k) s)
  rw [← Category.assoc, hp]
  apply NatTrans.ext
  funext k s
  change coprod.desc
      ((xiRowMappingIso C zeroIndex).hom.app k
        ((daggerVertexPoint (daggerCoherentNerve.obj C) x y 0).app k s))
      ((xiRowMappingIso C zeroIndex).hom.app k
        ((daggerVertexPoint (daggerCoherentNerve.obj C) x y 1).app k s)) =
    (endpointCollapse XiAugmentationCurried).app k.unop ≫
      boundaryTarget C (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat x)
        (OrdinaryRigidification.NerveVertices.vertexEquiv C.toSimplicialCat y)
  rw [vertexPoint_calibration, vertexPoint_calibration]
  apply coprod.hom_ext
  · simp only [endpointCollapse, coprod.inl_desc, coprod.inl_desc_assoc, Category.assoc]
  · simp only [endpointCollapse, coprod.inr_desc, coprod.inr_desc_assoc, Category.assoc]

end

end DaggerModels.PartII.JTXiOrderedPointCalibration
