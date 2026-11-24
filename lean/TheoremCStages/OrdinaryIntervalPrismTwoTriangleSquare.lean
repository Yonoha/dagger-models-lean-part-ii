import OrdinaryIntervalPrismConstantSection
import OrdinarySegalTwoTriangleUnitWeak

/-!
# The original constant interval section in the literal two-triangle square

The already checked square decomposition identifies the actual constant
section with the two inserted degeneracies, and the actual cotensor endpoint
arrow with the two outer faces. No weak-equivalence assertion is made here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryIntervalPrismTwoTriangleSquare

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalOrderedMappingFibres (endpointArrow)
open OrdinaryIntervalPrismMappingIso
open OrdinaryIntervalPrismConstantSection
open OrdinarySegalTwoTriangleUnitWeak

noncomputable section

/-- The checked literal square decomposition with its original two-triangle target. -/
def squareIso (W : Space) :
    (cotensor (Δ[1] : SSet.{0}) W).obj (op ⦋1⦌) ≅ twoTriangles W :=
  mappingIso W

/-- The actual constant interval section gives the two original degeneracies. -/
theorem constantSection_squareIso (W : Space) :
    (constantSection (Δ[1] : SSet.{0}) W).app (op ⦋1⦌) ≫ (squareIso W).hom =
      insertedTriangles W := by
  dsimp only [squareIso]
  apply pullback.hom_ext
  · erw [Category.assoc, mappingIso_lower]
    simpa only [insertedTriangles, pullback.lift_fst] using
      (constantSection_triangles W).1
  · erw [Category.assoc, mappingIso_upper]
    simpa only [insertedTriangles, pullback.lift_snd] using
      (constantSection_triangles W).2

/-- Both endpoint factors are calibrated by the same original row-zero iso. -/
def endpointIso (W : Space) :
    (cotensor (Δ[1] : SSet.{0}) W).obj (op ⦋0⦌) ⨯
        (cotensor (Δ[1] : SSet.{0}) W).obj (op ⦋0⦌) ≅
      W.obj (op ⦋1⦌) ⨯ W.obj (op ⦋1⦌) :=
  prod.mapIso (intervalZeroIso W) (intervalZeroIso W)

/-- The literal ordered endpoint arrow is the two outer edges of the square. -/
theorem squareIso_outerPair (W : Space) :
    (squareIso W).hom ≫ outerPair W =
      endpointArrow (cotensor (Δ[1] : SSet.{0}) W) ≫ (endpointIso W).hom := by
  dsimp only [squareIso]
  apply prod.hom_ext
  · simp only [outerPair, Category.assoc, prod.lift_fst,
      endpointIso, prod.mapIso_hom, prod.map_fst]
    erw [← Category.assoc, mappingIso_lower, ← Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointArrow_fst]
    exact (interval_source_endpoint W).symm
  · simp only [outerPair, Category.assoc, prod.lift_snd,
      endpointIso, prod.mapIso_hom, prod.map_snd]
    erw [← Category.assoc, mappingIso_upper, ← Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointArrow_snd]
    exact (interval_target_endpoint W).symm

/-- The actual degree-zero constant section is the original identity-arrow map. -/
theorem constantSection_app_zero (W : Space) :
    (constantSection (Δ[1] : SSet.{0}) W).app (op ⦋0⦌) ≫
        (intervalZeroIso W).hom =
      W.map (SimplexCategory.σ (0 : Fin 1)).op := by
  let d := W.map (SimplexCategory.δ (1 : Fin 2)).op
  have sd : W.map (SimplexCategory.σ (0 : Fin 1)).op ≫ d =
      𝟙 (W.obj (op ⦋0⦌)) :=
    SimplicialObject.δ_comp_σ_succ (X := W)
  have : Epi d := epi_of_epi_fac sd
  apply (cancel_epi d).mp
  dsimp only [d]
  rw [← Category.assoc]
  rw [(constantSection (Δ[1] : SSet.{0}) W).naturality,
    Category.assoc, interval_source_endpoint, ← Category.assoc,
    (constantSection_triangles W).1]
  exact SimplicialObject.δ_comp_σ_of_gt (X := W) (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide)

#print axioms constantSection_squareIso
#print axioms squareIso_outerPair
#print axioms constantSection_app_zero

end
end DaggerModels.PartII.OrdinaryIntervalPrismTwoTriangleSquare
