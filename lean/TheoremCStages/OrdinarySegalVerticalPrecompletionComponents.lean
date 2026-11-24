import OrdinarySegalVerticalPrecompletion
import NativeKanRigHomWeakRecognition
import Mathlib.CategoryTheory.Types.Basic

/-!
# Object-component coverage of the correctly indexed precompletion unit

The vertical-zero isomorphism supplies a bijection on the vertices of every
horizontal row. The existing simplicial component-surjectivity theorem then
applies to each actual row of the unit. No Segal, completeness, or mapping-fiber
weakness claim is needed or asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalVerticalPrecompletionComponents

open OrdinaryCSSLocalization (Space)
open OrdinarySegalVerticalPrecompletion (unit precompletion)

noncomputable section

/-- The unit is bijective on the original vertices in each horizontal degree. -/
theorem unit_vertices_bijective (W : Space) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (((unit W).app n).app (op ⦋0⦌)) := by
  have : IsIso (NatTrans.flipApp (unit W) (op ⦋0⦌)) :=
    OrdinarySegalVerticalPrecompletion.unit_verticalZero_isIso W
  exact (CategoryTheory.isIso_iff_bijective
    ((NatTrans.flipApp (unit W) (op ⦋0⦌)).app n)).mp inferInstance

/-- Every component of each original precompletion row has a unit preimage. -/
theorem unit_row_components_surjective (W : Space) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (SSet.mapπ₀ ((unit W).app n)) :=
  DaggerNativeKanRigHomWeakRecognition.mapπ₀_surjective_of_vertices
    ((unit W).app n) (unit_vertices_bijective W n).surjective

/-- In particular the actual object-space component map is surjective. -/
theorem unit_object_components_surjective (W : Space) :
    Function.Surjective (SSet.mapπ₀ ((unit W).app (op ⦋0⦌))) :=
  unit_row_components_surjective W (op ⦋0⦌)

#print axioms unit_vertices_bijective
#print axioms unit_row_components_surjective
#print axioms unit_object_components_surjective

end
end DaggerModels.PartII.OrdinarySegalVerticalPrecompletionComponents
