import OrdinarySegalCotensorProductParameterNaturality
import OrdinarySegalCotensorProductUnit
import OrdinarySegalCotensorPointEvaluation

/-!
# Actual parameter homotopies induce whole cotensor homotopies

The source and time parameters retain their original order. The checked
product isomorphism transposes the whole parameter homotopy, and its
outer-parameter naturality and unit comparison identify both exact endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalCotensorParameterHomotopy

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalCotensorProductIso (productIso)
open OrdinarySegalCotensorPointEvaluation (evaluation)

noncomputable section

/-- Transpose the whole original parameter homotopy, not its objectwise slices. -/
def homotopy {K L T : SSet.{0}} (H : K ⊗ T ⟶ L) (W : Space) :
    cotensor L W ⟶ cotensor T (cotensor K W) :=
  pre H W ≫ (productIso T K W).inv

/-- Every original time vertex evaluates to restriction along the actual
tensor slice, including its original right unitor. -/
theorem homotopy_evaluation {K L T : SSet.{0}} (H : K ⊗ T ⟶ L) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ T) :
    homotopy H W ≫ evaluation T (cotensor K W) v =
      pre ((SSet.stdSimplex.rightUnitor K).inv ≫ K ◁ v ≫ H) W := by
  let F := productIso T K W
  let U := productIso (Δ[0] : SSet.{0}) K W
  let A := pre v (cotensor K W)
  let B := pre (K ◁ v) W
  have h : A ≫ U.hom = F.hom ≫ B :=
    OrdinarySegalCotensorProductParameterNaturality.productIso_natural_outer K v W
  have hi : F.inv ≫ A = B ≫ U.inv := by
    apply (cancel_mono U.hom).mp
    rw [Category.assoc, h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (pre H W ≫ F.inv) ≫
      (A ≫ (OrdinarySegalHorizontalCotensorPoint.pointIso (cotensor K W)).hom) = _
  rw [Category.assoc, ← Category.assoc F.inv, hi, Category.assoc B,
    OrdinarySegalCotensorProductUnit.point_product_inv]
  rw [← OrdinarySegalHorizontalCotensor.pre_comp,
    ← OrdinarySegalHorizontalCotensor.pre_comp, Category.assoc]

#print axioms homotopy_evaluation

end
end DaggerModels.PartII.OrdinarySegalCotensorParameterHomotopy
