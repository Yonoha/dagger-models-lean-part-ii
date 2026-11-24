import DaggerModelsPartII.JTCylinderConeComparison
import DaggerModelsPartII.JTEndpointObjects
import DaggerModelsPartII.EndpointMappingFiber
import ActualGeneralRightConeMapping

/-!
# The literal under-boundary Hom is the original right-cone mapping space

Maps from the original cone under the ordered one-boundary amount to maps
from that same cone with its collapsed and terminal vertices fixed. The
equivalence is natural in every simplex operator and retains the underlying
cone map of each simplex.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTConeMappingPresentation

open JTXiEndpointCollapse JTCylinderConeComparison JTEndpointObjects
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor

noncomputable section

/-- The specified pair of ordinary vertices as an actual map out of the
literal ordered boundary. -/
def orderedBoundary (X : SSet.{0}) (x y : X.obj (op ⦋0⦌)) :
    JTXiEndpointCollapse.boundary ⟶ X :=
  (boundaryHomEquiv X).symm (x, y)

/-- The actual target object under the literal boundary. -/
def targetUnder (X : SSet.{0}) (x y : X.obj (op ⦋0⦌)) :
    Under JTXiEndpointCollapse.boundary :=
  Under.mk (orderedBoundary X x y)

/-- Restriction along the two formal cone vertices reads exactly the
collapsed and terminal vertices of the original cone map. -/
theorem coneBoundary_pair (X : SSet.{0}) (k : SimplexCategory)
    (σ : cone.{0} k.len ⟶ X) :
    boundaryHomEquiv X (coneBoundary k ≫ σ) =
      (σ.app (op ⦋0⦌) (alpha.{0} k.len),
        σ.app (op ⦋0⦌) (omega.{0} k.len)) := by
  have hzero : SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})) =
      SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  apply Prod.ext
  · change SSet.yonedaEquiv
        (SSet.boundary₁.ι₀ ≫ (coneBoundary k ≫ σ)) = _
    rw [← Category.assoc, coneBoundary_zero, SSet.yonedaEquiv_comp]
    change σ.app (op ⦋0⦌)
      ((alphaMap.{0} k.len).app (op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))) = _
    rw [hzero]
    rfl
  · change SSet.yonedaEquiv
        (SSet.boundary₁.ι₁ ≫ (coneBoundary k ≫ σ)) = _
    rw [← Category.assoc, coneBoundary_one, SSet.yonedaEquiv_comp]
    change σ.app (op ⦋0⦌)
      ((omegaMap.{0} k.len).app (op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))) = _
    rw [hzero]
    rfl

/-- The under-boundary equation is precisely the native pair of endpoint
equations, in the manuscript's specified order. -/
theorem boundary_iff_endpoints (X : SSet.{0})
    (x y : X.obj (op ⦋0⦌)) (k : SimplexCategory)
    (σ : cone.{0} k.len ⟶ X) :
    coneBoundary k ≫ σ = orderedBoundary X x y ↔
      σ.app (op ⦋0⦌) (alpha.{0} k.len) = x ∧
        σ.app (op ⦋0⦌) (omega.{0} k.len) = y := by
  constructor
  · intro h
    have hp := congrArg (boundaryHomEquiv X) h
    rw [coneBoundary_pair, orderedBoundary, Equiv.apply_symm_apply] at hp
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · intro h
    apply (boundaryHomEquiv X).injective
    rw [coneBoundary_pair, orderedBoundary, Equiv.apply_symm_apply]
    exact Prod.ext h.1 h.2

/-- At every degree, under-boundary morphisms are the literal native
right-cone mapping simplices. -/
def coneHomEquiv (X : SSet.{0}) (x y : X.obj (op ⦋0⦌))
    (k : SimplexCategory) :
    (coneUnder.obj k ⟶ targetUnder X x y) ≃
      (DaggerActualGeneralRightConeMapping.rightMapping X x y).obj (op k) where
  toFun f := ⟨f.right, (boundary_iff_endpoints X x y k f.right).mp (by
    have hw := f.w
    change orderedBoundary X x y = coneBoundary k ≫ f.right at hw
    exact hw.symm)⟩
  invFun σ := Under.homMk σ.val
    ((boundary_iff_endpoints X x y k σ.val).mpr σ.property)
  left_inv f := by
    apply Under.UnderMorphism.ext
    rfl
  right_inv σ := by
    apply Subtype.ext
    rfl

/-- The component equivalence preserves the underlying original cone map
literally, before any weak-equivalence comparison. -/
theorem coneHomEquiv_val (X : SSet.{0}) (x y : X.obj (op ⦋0⦌))
    (k : SimplexCategory) (f : coneUnder.obj k ⟶ targetUnder X x y) :
    (coneHomEquiv X x y k f).val = f.right := rfl

/-- The strict under-boundary Hom simplicial set is isomorphic to the
original right-cone mapping simplicial set for all simplex operators. -/
def coneMappingIso (X : SSet.{0}) (x y : X.obj (op ⦋0⦌)) :
    EndpointMappingFiber.mapping (Z := targetUnder X x y) coneUnder ≅
      DaggerActualGeneralRightConeMapping.rightMapping X x y :=
  NatIso.ofComponents (fun q ↦ (coneHomEquiv X x y q.unop).toIso) (by
    intro q r θ
    funext f
    apply Subtype.ext
    change ((coneUnder.map θ.unop ≫ f).right) =
      coneMap.{0} θ.unop ≫ f.right
    rfl)

/-- On each simplex, the isomorphism has the actual right leg as its value. -/
theorem coneMappingIso_hom_val (X : SSet.{0}) (x y : X.obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ)
    (f : coneUnder.obj q.unop ⟶ targetUnder X x y) :
    ((coneMappingIso X x y).hom.app q f).val = f.right := rfl

end

end DaggerModels.PartII.JTConeMappingPresentation
