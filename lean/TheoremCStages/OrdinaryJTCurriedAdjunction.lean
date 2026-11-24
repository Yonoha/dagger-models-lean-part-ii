import OrdinaryJTNativeRightNerveReedy
import DaggerModelsPartII.JTRealizationDiagonal
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual ordinary JT adjunction after currying

`Functor.currying` and `prodOpEquiv.congrLeft` supply the existing
index equivalence. Composing its inverse adjunction with the original
`realizationNerveAdjunction` keeps the same two-index realization and nerve.
This is an adjunction of categories; no Quillen-equivalence claim is made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTCurriedAdjunction

noncomputable section

/-- The existing currying operation packaged as its actual equivalence. -/
def curryEquivalence : OrdinaryJTRealization.BiPresheaf ≌
    (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  ((prodOpEquiv (C := SimplexCategory)
    (D := SimplexCategory)).symm.congrLeft).symm.trans Functor.currying.symm

/-- This equivalence uses exactly the previously defined curry functor. -/
theorem curryEquivalence_functor :
    curryEquivalence.functor = JTRealizationDiagonal.ordinaryCurry := rfl

/-- The original realization with the two indices uncurried by the equivalence. -/
def left : (SimplexCategoryᵒᵖ ⥤ SSet.{0}) ⥤ SSet.{0} :=
  curryEquivalence.inverse ⋙ OrdinaryJTRealization.realization

/-- The literal original restricted-Yoneda nerve with its indices curried. -/
def right : SSet.{0} ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  OrdinaryJTRealization.nerve ⋙ JTRealizationDiagonal.ordinaryCurry

/-- The categorical adjunction is transported through the existing equivalence. -/
def adjunction : left ⊣ right :=
  curryEquivalence.symm.toAdjunction.comp
    OrdinaryJTRealization.realizationNerveAdjunction

/-- Its objects are exactly the native diagrams whose Reedy fibrancy was checked. -/
theorem right_obj (X : SSet.{0}) :
    right.obj X = OrdinaryJTNativeRightNerveReedy.nativeSpace X := rfl

/-- Every morphism retains the original two-index component of the nerve. -/
theorem right_map_app_app {X Y : SSet.{0}} (p : X ⟶ Y)
    (m k : SimplexCategory) :
    ((right.map p).app (op m)).app (op k) =
      (OrdinaryJTRealization.nerve.map p).app (op (m, k)) := rfl

private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  simplicialReedyModelCategory SSet.{0}

/-- The actual right adjoint takes quasicategories to Reedy fibrant diagrams. -/
theorem right_obj_reedyFibrant (X : SSet.{0}) [X.Quasicategory] :
    IsFibrant (right.obj X) :=
  OrdinaryJTNativeRightNerveReedy.nativeSpace_reedyFibrant X

#print axioms curryEquivalence
#print axioms adjunction
#print axioms right_map_app_app
#print axioms right_obj_reedyFibrant

end

end DaggerModels.PartII.OrdinaryJTCurriedAdjunction
