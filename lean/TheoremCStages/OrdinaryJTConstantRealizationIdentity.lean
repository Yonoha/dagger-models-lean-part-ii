import OrdinaryJTFirstRowIdentity
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The ordinary JT realization of a vertically constant simplicial set

Precomposition by the first projection is left adjoint to evaluation at
the second degree zero because `[0]` is terminal in `SimplexCategory`.
Composing with the literal JT realization--nerve adjunction and using the
checked natural isomorphism `nerve ⋙ firstRow ≅ 𝟭 SSet` gives the claimed
strict natural isomorphism by uniqueness of left adjoints. This is a
functor-level identity, not a Quillen-equivalence or derived-unit claim.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryJTConstantRealizationIdentity

open OrdinaryJTRealization OrdinaryJTFirstRowIdentity

noncomputable section

/-- The first projection on the actual two-simplex index. -/
def firstProjection : Index ⥤ SimplexCategory :=
  CategoryTheory.Prod.fst SimplexCategory SimplexCategory

/-- Vertically constant bisimplicial presheaf with original first-index values. -/
def p1Constant : SSet.{0} ⥤ BiPresheaf :=
  (Functor.whiskeringLeft _ _ _).obj firstProjection.op

/-- The first projection is left adjoint to the zero-section in the index. -/
def firstProjectionAdjunction :
    firstProjection ⊣ CategoryTheory.Prod.sectL SimplexCategory ⦋0⦌ where
  unit := {
    app := fun X => (𝟙 X.1, SimplexCategory.isTerminalZero.from X.2)
    naturality := by
      intro X Y f
      apply Prod.hom_ext
      · simp [firstProjection]
      · exact SimplexCategory.isTerminalZero.hom_ext _ _ }
  counit := 𝟙 _
  left_triangle_components X := by
    rfl
  right_triangle_components Y := by
    apply Prod.hom_ext
    · simp [firstProjection]
    · exact SimplexCategory.isTerminalZero.hom_ext _ _

/-- Literal vertical constancy is left adjoint to the checked first-row functor. -/
def p1ConstantAdjunction : p1Constant ⊣ firstRow :=
  Adjunction.whiskerLeft (Type 0) firstProjectionAdjunction.op

/-- The composite right adjoint is the first row of the original JT nerve. -/
def compositeAdjunction :
    p1Constant ⋙ realization ⊣ nerve ⋙ firstRow :=
  p1ConstantAdjunction.comp realizationNerveAdjunction

/-- The actual JT realization of a vertically constant simplicial set is
naturally the original simplicial set, including its original target model. -/
def realizationIdentityIso : p1Constant ⋙ realization ≅ 𝟭 SSet.{0} :=
  (compositeAdjunction.ofNatIsoRight nerveFirstRowIso).leftAdjointUniq Adjunction.id

#print axioms firstProjectionAdjunction
#print axioms p1ConstantAdjunction
#print axioms compositeAdjunction
#print axioms realizationIdentityIso

end

end DaggerModels.PartII.OrdinaryJTConstantRealizationIdentity
