import OrdinarySegalCotensorMappingIso
import OrdinarySegalWalkingEvaluation

/-!
# Calibrating Fubini on the original horizontal representables

At a standard simplex, the exact Fubini map evaluates the same original
horizontal identity simplex as the checked representable mapping map.
The codomain is the literal row of the unchanged horizontal cotensor.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed

namespace DaggerModels.PartII.OrdinarySegalCotensorSimplexCalibration

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)

noncomputable section

private theorem row_yoneda (K : SSet.{0}) (W : Space)
    (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (g : (Δ[n] : SSet.{0}) ⟶ (cotensor K W).flip.obj q) :
    uncurry (g ≫ (OrdinarySegalCotensorMappingIso.rowIso K W q).hom) =
      (OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ (Δ[n] : SSet.{0})) W q.unop)
          (SSet.yonedaEquiv (X := (cotensor K W).flip.obj q) (n := ⦋n⦌) g) := by
  have hy : g ≫ (OrdinarySegalCotensorMappingIso.rowIso K W q).hom =
      SSet.yonedaEquiv.symm
        ((OrdinarySegalCotensorMappingIso.rowIso K W q).hom.app
          (op ⦋n⦌) (SSet.yonedaEquiv (X := (cotensor K W).flip.obj q) (n := ⦋n⦌) g)) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hr :
      (OrdinarySegalCotensorMappingIso.rowIso K W q).hom.app
          (op ⦋n⦌) (SSet.yonedaEquiv (X := (cotensor K W).flip.obj q) (n := ⦋n⦌) g) =
        SSet.yonedaEquiv
          (curry ((OrdinaryDiscreteMapping.levelEquiv
            (K ⊗ (Δ[n] : SSet.{0})) W q.unop)
          (SSet.yonedaEquiv (X := (cotensor K W).flip.obj q) (n := ⦋n⦌) g))) := rfl
  rw [hy, hr, Equiv.symm_apply_apply, uncurry_curry]

/-- Both maps have the exact same source and the original cotensor row as
their definitional codomain. -/
theorem mappingIso_simplex_hom (K : SSet.{0}) (W : Space) (n : ℕ) :
    (OrdinarySegalCotensorMappingIso.mappingIso K (Δ[n] : SSet.{0}) W).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso (cotensor K W) n).hom := by
  apply NatTrans.ext
  funext q t
  apply (OrdinaryDiscreteMapping.levelEquiv
    (K ⊗ (Δ[n] : SSet.{0})) W q.unop).injective
  have hm :
      (OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ (Δ[n] : SSet.{0})) W q.unop)
          ((OrdinarySegalCotensorMappingIso.mappingIso K (Δ[n] : SSet.{0}) W).hom.app
            q t) =
        uncurry ((OrdinaryDiscreteMapping.levelEquiv
          (Δ[n] : SSet.{0}) (cotensor K W) q.unop) t ≫
            (OrdinarySegalCotensorMappingIso.rowIso K W q).hom) := by
    change (OrdinaryDiscreteMapping.levelEquiv
        (K ⊗ (Δ[n] : SSet.{0})) W q.unop)
        ((OrdinaryDiscreteMapping.levelEquiv
          (K ⊗ (Δ[n] : SSet.{0})) W q.unop).symm
          (uncurry ((OrdinaryDiscreteMapping.levelEquiv
            (Δ[n] : SSet.{0}) (cotensor K W) q.unop) t ≫
              (OrdinarySegalCotensorMappingIso.rowIso K W q).hom))) = _
    exact Equiv.apply_symm_apply _ _
  have hs :
      (OrdinarySegalWalkingEvaluation.simplexMappingIso (cotensor K W) n).hom.app
          q t =
        SSet.yonedaEquiv ((OrdinaryDiscreteMapping.levelEquiv
          (Δ[n] : SSet.{0}) (cotensor K W) q.unop) t) := rfl
  rw [hm, hs]
  exact row_yoneda K W n q _

#print axioms mappingIso_simplex_hom

end
end DaggerModels.PartII.OrdinarySegalCotensorSimplexCalibration
