import DaggerModelsPartII.JTZeroObjects
import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.Loop
import DaggerModels.DaggerDiscreteObjects

/-!
# The literal free dagger one-boundary classifies ordered objects

The two vertices of the actual simplicial boundary `∂Δ[1]` give its
binary-coproduct universal property. The original free dagger and dagger
rigidification adjunctions transfer this property to the manuscript's
two-object boundary, with its vertex order fixed.
-/

set_option autoImplicit false

open CategoryTheory Simplicial DaggerModels
open DaggerModels.OrdinaryRigidification

namespace DaggerModels.PartII.JTEndpointObjects

noncomputable section

open JTZeroObjects

/-- The manuscript's literal simplicial one-boundary. -/
def boundary : SSet.{0} := (SSet.boundary 1).toSSet

/-- The `i`-th vertex as an element of the literal boundary. -/
def boundaryVertex (i : Fin 2) : boundary.obj (Opposite.op ⦋0⦌) :=
  ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ i), by
    change ¬Function.Surjective (fun _ : Fin 1 ↦ i)
    intro h
    obtain ⟨a, ha⟩ := h 0
    obtain ⟨b, hb⟩ := h 1
    exact (by decide : (0 : Fin 2) ≠ 1) (ha.symm.trans hb)⟩

/-- The two ordered inclusions `Δ[0] → ∂Δ[1]`. -/
def boundaryVertexMap (i : Fin 2) : (Δ[0] : SSet.{0}) ⟶ boundary :=
  SSet.yonedaEquiv.symm (boundaryVertex i)

private theorem boundaryVertexMap_zero :
    boundaryVertexMap 0 = SSet.boundary₁.ι₀ := by
  apply (cancel_mono (SSet.boundary 1).ι).mp
  apply SSet.yonedaEquiv.injective
  rw [SSet.boundary₁.ι₀_ι]
  rw [SSet.stdSimplex.δ_one]
  simp only [SSet.yonedaEquiv_comp, boundaryVertexMap, Equiv.apply_symm_apply]
  rfl

private theorem boundaryVertexMap_one :
    boundaryVertexMap 1 = SSet.boundary₁.ι₁ := by
  apply (cancel_mono (SSet.boundary 1).ι).mp
  apply SSet.yonedaEquiv.injective
  rw [SSet.boundary₁.ι₁_ι]
  rw [SSet.stdSimplex.δ_zero]
  simp only [SSet.yonedaEquiv_comp, boundaryVertexMap, Equiv.apply_symm_apply]
  rfl

/-- A map out of the actual one-boundary is a pair of vertices. -/
def boundaryHomEquiv (X : SSet.{0}) :
    (boundary ⟶ X) ≃ X.obj (Opposite.op ⦋0⦌) × X.obj (Opposite.op ⦋0⦌) where
  toFun f := (SSet.yonedaEquiv (SSet.boundary₁.ι₀ ≫ f),
    SSet.yonedaEquiv (SSet.boundary₁.ι₁ ≫ f))
  invFun p := SSet.boundary₁.desc p.1 p.2
  left_inv f := by
    apply SSet.boundary₁.hom_ext
    · simp only [SSet.boundary₁.ι₀_desc, Equiv.symm_apply_apply]
    · simp only [SSet.boundary₁.ι₁_desc, Equiv.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · simp only [SSet.boundary₁.ι₀_desc, Equiv.apply_symm_apply]
    · simp only [SSet.boundary₁.ι₁_desc, Equiv.apply_symm_apply]

/-- The original dagger simplicial-set boundary and its rigidification. -/
def B : DaggerSSet.{0} := freeDagger.obj boundary

def Bdagger : DaggerSimplicialCat.{0, 0} :=
  DaggerRigidification.daggerRigidification.obj B

/-- The specified ordered endpoint inclusions from the actual zero frame. -/
def endpointMap (i : Fin 2) : RigidifiedJTFrames.A.obj zeroIndex ⟶ Bdagger :=
  zeroInputIso.hom ≫
    DaggerRigidification.daggerRigidification.map (freeDagger.map (boundaryVertexMap i))

/-- Actual boundary Hom equivalence through the two original adjunctions. -/
def boundaryObjectsEquiv (C : DaggerSimplicialCat.{0, 0}) :
    (Bdagger ⟶ C) ≃ C.Obj × C.Obj :=
  (DaggerAdjunction.homEquiv B C).trans
    ((freeDaggerAdjunction.homEquiv boundary
      (DaggerNerve.daggerCoherentNerve.obj C)).trans
    ((boundaryHomEquiv (DaggerNerve.daggerCoherentNerve.obj C).toSSet).trans
      (Equiv.prodCongr (NerveVertices.vertexEquiv C.toSimplicialCat)
        (NerveVertices.vertexEquiv C.toSimplicialCat))))

private theorem zeroHomEquiv_endpoint (C : DaggerSimplicialCat.{0, 0})
    (f : Bdagger ⟶ C) (v : (Δ[0] : SSet.{0}) ⟶ boundary) :
    zeroHomEquiv C
      (zeroInputIso.hom ≫
        DaggerRigidification.daggerRigidification.map (freeDagger.map v) ≫ f) =
      NerveVertices.vertexEquiv C.toSimplicialCat
        (SSet.yonedaEquiv
          (v ≫ freeDaggerAdjunction.homEquiv boundary
            (DaggerNerve.daggerCoherentNerve.obj C)
              (DaggerAdjunction.homEquiv B C f))) := by
  have hdag :=
    DaggerAdjunction.daggerRigidificationCoherentNerveAdjunction.homEquiv_naturality_left
      (freeDagger.map v) f
  rw [DaggerAdjunction.adjunction_homEquiv] at hdag
  have hfree := freeDaggerAdjunction.homEquiv_naturality_left v
    (DaggerAdjunction.homEquiv B C f)
  dsimp only [B] at hfree
  simp only [zeroHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [hdag, hfree]
  rfl

/-- The equivalence reads precisely the two specified endpoint maps. -/
theorem boundaryObjectsEquiv_apply (C : DaggerSimplicialCat.{0, 0}) (f : Bdagger ⟶ C) :
    boundaryObjectsEquiv C f =
      (zeroHomEquiv C (endpointMap 0 ≫ f),
        zeroHomEquiv C (endpointMap 1 ≫ f)) := by
  apply Prod.ext
  · simpa only [boundaryObjectsEquiv, Equiv.trans_apply,
      boundaryHomEquiv, Equiv.prodCongr_apply, endpointMap,
      boundaryVertexMap_zero] using (zeroHomEquiv_endpoint C f SSet.boundary₁.ι₀).symm
  · simpa only [boundaryObjectsEquiv, Equiv.trans_apply,
      boundaryHomEquiv, Equiv.prodCongr_apply, endpointMap,
      boundaryVertexMap_one] using (zeroHomEquiv_endpoint C f SSet.boundary₁.ι₁).symm

/-- The public ordered-pair classification uses the literal endpoint formula. -/
def boundaryPairEquiv (C : DaggerSimplicialCat.{0, 0}) :
    (Bdagger ⟶ C) ≃ C.Obj × C.Obj := boundaryObjectsEquiv C

@[simp] theorem boundaryPairEquiv_apply (C : DaggerSimplicialCat.{0, 0})
    (f : Bdagger ⟶ C) :
    boundaryPairEquiv C f =
      (zeroHomEquiv C (endpointMap 0 ≫ f),
        zeroHomEquiv C (endpointMap 1 ≫ f)) :=
  boundaryObjectsEquiv_apply C f

/-- The zero frame is canonically the concrete one-object dagger category. -/
def zeroPointIso : RigidifiedJTFrames.A.obj zeroIndex ≅
    DaggerDiscreteObjects.point.{0, 0} where
  hom := DaggerDiscreteObjects.toPoint _
  inv := DaggerDiscreteObjects.fromPoint _ zeroObject
  hom_inv_id := by
    apply (zeroHomEquiv _).injective
    rw [zeroHomEquiv_eq_obj, zeroHomEquiv_eq_obj]
    rfl
  inv_hom_id := by
    apply (DaggerDiscreteObjects.pointHomEquiv _).injective
    rfl

end

end DaggerModels.PartII.JTEndpointObjects
