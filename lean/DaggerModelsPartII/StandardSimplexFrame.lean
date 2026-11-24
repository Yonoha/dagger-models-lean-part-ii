import DaggerModelsPartII.SimplexBoundaryColimit
import DaggerModelsPartII.ReedyFibrantDiagrams
import TopCatModelCategory.ModelCategorySSet

/-!
# The standard simplex as a Reedy fibrant opposite diagram

The matching object in the opposite Kan model is the opposite of the
ordinary boundary of the standard simplex.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII

noncomputable section

local instance standardFrameReedyModel : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ SSet.{u}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{u}ᵒᵖ

/-- The proper-face matching object is the opposite of the standard boundary. -/
def matchingBoundaryIso (n : ℕ) :
    (matchingFunctor n).obj SSet.stdSimplex.{u}.op ≅ op (SSet.boundary.{u} n).toSSet :=
  limit.isoLimitCone ⟨coneOfCoconeLeftOp
    (F := matchingProjection n ⋙ SSet.stdSimplex.{u}.op) (boundaryFaceCocone.{u} n),
    isLimitConeOfCoconeLeftOp _ (boundaryFaceIsColimit.{u} n)⟩

/-- The Reedy matching comparison is the opposite of the boundary inclusion. -/
theorem matchingBoundaryIso_comp (n : ℕ) :
    (matchingComparison n).app SSet.stdSimplex.{u}.op ≫ (matchingBoundaryIso.{u} n).hom =
      (SSet.boundary.{u} n).ι.op := by
  apply Quiver.Hom.unop_inj
  apply (boundaryFaceIsColimit.{u} n).hom_ext
  intro s
  apply Quiver.Hom.op_inj
  change ((matchingComparison n).app SSet.stdSimplex.{u}.op ≫
      (matchingBoundaryIso.{u} n).hom) ≫ (boundaryFaceInclusion s.unop).op =
    (SSet.stdSimplex.map s.unop.obj.hom.unop).op
  rw [Category.assoc]
  have hlim : (matchingBoundaryIso.{u} n).hom ≫
      (boundaryFaceInclusion s.unop).op =
      limit.π (matchingProjection n ⋙ SSet.stdSimplex.{u}.op) s.unop := by
    exact limit.isoLimitCone_hom_π
      ⟨coneOfCoconeLeftOp
        (F := matchingProjection n ⋙ SSet.stdSimplex.{u}.op) (boundaryFaceCocone.{u} n),
        isLimitConeOfCoconeLeftOp _ (boundaryFaceIsColimit.{u} n)⟩ s.unop
  rw [hlim]
  exact limit.lift_π _ _

/-- The opposite standard-simplex diagram is Reedy fibrant in the opposite Kan model. -/
theorem standardSimplex_op_reedyFibrant : IsFibrant SSet.stdSimplex.{u}.op := by
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  apply ((fibrations SSet.{u}ᵒᵖ).cancel_right_of_respectsIso
    ((matchingComparison n).app SSet.stdSimplex.{u}.op)
    (matchingBoundaryIso.{u} n).hom).mp
  rw [matchingBoundaryIso_comp]
  rw [fibrations_op]
  exact (cofibration_iff _).mp
    ((SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance)

end

end DaggerModels.PartII
