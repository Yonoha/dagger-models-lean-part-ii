import OrdinaryZeroCoskeleton
import DaggerModelsPartII.DiagramTensorMappingAdjunction

/-!
# Discrete horizontal tests on the ordinary zero coskeleton

The existing evaluation adjunction makes tests invertible when their
zero components are invertible. Every original spine contains all vertices.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryZeroCoskeletonMapping

open OrdinaryZeroCoskeleton

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev S := OrdinaryCSSLocalization.Space
private abbrev zero : J := op ⦋0⦌
private abbrev adj := evaluationAdjunctionLeft SSet.{0} zero

/-- Every whole simplicial mapping degree out of a map which is invertible
at zero is invertible under restriction into the actual zero coskeleton. -/
theorem precomp_isIso {A B : S} (i : A ⟶ B) [IsIso (i.app zero)] (K : SSet.{0}) :
    IsIso (diagramMappingPrecomp i (coskeleton.obj K)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  let T := tensorRight (SSet.stdSimplex.obj q.unop)
  let j := Functor.whiskerRight i T
  haveI : IsIso (j.app zero) := inferInstanceAs (IsIso (T.map (i.app zero)))
  let eA := adj.homEquiv ((diagramTensor A).obj (SSet.stdSimplex.obj q.unop)) K
  let eB := adj.homEquiv ((diagramTensor B).obj (SSet.stdSimplex.obj q.unop)) K
  let e := eB.symm.trans (((asIso (j.app zero)).symm.homCongr (Iso.refl K)).trans eA)
  have h (g : (diagramMappingSpace B (coskeleton.obj K)).obj q) :
      (diagramMappingPrecomp i (coskeleton.obj K)).app q g = e g := by
    apply eA.symm.injective
    change eA.symm (j ≫ g) = eA.symm (eA ((j.app zero ≫ eB.symm g) ≫ 𝟙 K))
    rw [Equiv.symm_apply_apply, Category.comp_id]
    exact adj.homEquiv_naturality_left_symm j g
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    apply e.injective
    exact (h x).symm.trans (hxy.trans (h y))
  · intro y
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, (h x).trans hx⟩

/-- The original ordinary spine inclusion is an isomorphism on the zero row. -/
theorem spineMap_zero_isIso (n : ℕ) :
    IsIso ((OrdinaryCSSLocalization.spineMap n).app zero) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  apply (isIso_iff_bijective _).mpr
  change Function.Bijective
    (Subtype.val : (DaggerNativeStandardSpineInner.spine n).obj (op ⦋0⦌) →
      (Δ[n] : SSet.{0}).obj (op ⦋0⦌))
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  have hx : x ∈ (DaggerNativeStandardSpineInner.spine n).obj (op ⦋0⦌) := by
    rw [DaggerNativeStandardSpineInner.mem_spine_iff]
    have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hlast]
    omega
  exact ⟨⟨x, hx⟩, rfl⟩

#print axioms precomp_isIso
#print axioms spineMap_zero_isIso

end

end DaggerModels.PartII.OrdinaryZeroCoskeletonMapping
