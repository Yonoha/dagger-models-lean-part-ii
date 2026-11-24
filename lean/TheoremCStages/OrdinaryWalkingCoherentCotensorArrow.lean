import OrdinaryWalkingCoherentContraction
import OrdinarySegalCotensorMappingIso

/-!
# Currying the coherent walking contraction into the original cotensor

For each full horizontal parameter map `z`, the same groupoid-time
contraction gives a coherent walking arrow in the actual cotensor row.
The tensor-source endpoint equations are retained before calibration
against the original constant-section object.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed

namespace DaggerModels.PartII.OrdinaryWalkingCoherentCotensorArrow

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalCotensorMappingIso (rowIso)
open OrdinaryWalkingCoherentContraction
  (contraction slice contraction_zero contraction_one)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The whole coherent walking arrow in the actual horizontal cotensor row. -/
def arrow (W : Space) (q : SimplexCategoryᵒᵖ)
    (z : E ⟶ W.flip.obj q) (j : Fin 2) :
    E ⟶ (cotensor E W).flip.obj q :=
  curry (contraction j ≫ z) ≫ (rowIso E W q).inv

/-- The row identification reads the arrow as the original whole-map curry. -/
theorem arrow_rowIso (W : Space) (q : SimplexCategoryᵒᵖ)
    (z : E ⟶ W.flip.obj q) (j : Fin 2) :
    arrow W q z j ≫ (rowIso E W q).hom = curry (contraction j ≫ z) := by
  rw [arrow, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The first complete tensor endpoint is the prescribed parameter map. -/
theorem arrow_first_tensor (W : Space) (q : SimplexCategoryᵒᵖ)
    (z : E ⟶ W.flip.obj q) (j : Fin 2) :
    slice 0 ≫ uncurry (arrow W q z j ≫ (rowIso E W q).hom) = z := by
  rw [arrow_rowIso, uncurry_curry, ← Category.assoc, contraction_zero,
    Category.id_comp]

/-- The second complete tensor endpoint is the actual parameter map
constant at `j`, followed by the same prescribed map `z`. -/
theorem arrow_second_tensor (W : Space) (q : SimplexCategoryᵒᵖ)
    (z : E ⟶ W.flip.obj q) (j : Fin 2) :
    slice 1 ≫ uncurry (arrow W q z j ≫ (rowIso E W q).hom) =
      JTParameterContraction.constantAt ⦋1⦌ j ≫ z := by
  rw [arrow_rowIso, uncurry_curry, ← Category.assoc, contraction_one]

#print axioms arrow_rowIso
#print axioms arrow_first_tensor
#print axioms arrow_second_tensor

end
end DaggerModels.PartII.OrdinaryWalkingCoherentCotensorArrow
