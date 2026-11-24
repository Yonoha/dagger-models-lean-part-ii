import DaggerModelsPartII.GroupoidSimplex
import NativeOrdinaryDaggerNerveLift

/-!
# Inversion and reversal of the groupoid-simplex parameter

The ordinary dagger is actual groupoid inversion. The retained native dagger
nerve supplies involutivity, fixed vertices and all simplicial reversal laws;
the parameter functors preserve this dagger in every simplex degree.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.GroupoidSimplexReversal

open GroupoidSimplex

noncomputable section

private local instance completionThin (k : SimplexCategory) : Quiver.IsThin (completion k) :=
  DaggerOriginalInitialCategoryCompletionThin.completionIsThin
    (0 : Fin (k.len + 1)) (Fin.isInitialZero _)

private local instance completionFunctorGroupoid (k : SimplexCategory) :
    Groupoid (completionFunctor.obj k) := inferInstanceAs (Groupoid (completion k))

private local instance completionDagger (k : SimplexCategory) : DaggerCategory (completion k) where
  dagger f := Groupoid.inv f
  dagger_involutive _ := Subsingleton.elim _ _
  dagger_id _ := Subsingleton.elim _ _
  dagger_comp _ _ := Subsingleton.elim _ _

/-- The same actual parameter, equipped with inversion of reversed chains. -/
def daggerParameter : SimplexCategory ⥤ DaggerSSet.{0} where
  obj k := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (completion k)
  map {k l} f := {
    hom := parameter.map f
    comm := by
      apply NatTrans.ext
      funext n ξ
      apply nerve.ext_of_isThin
      funext i
      rfl }
  map_id k := by
    apply DaggerSSet.Hom.ext
    exact parameter.map_id k
  map_comp f g := by
    apply DaggerSSet.Hom.ext
    exact parameter.map_comp f g

/-- Forgetting the specified dagger leaves exactly the earlier Kan parameter. -/
theorem underlying_eq : daggerParameter ⋙ DaggerSSet.forget = parameter := rfl

/-- Reversal retains the original objects in reversed order. -/
theorem reversal_objects (k n : SimplexCategory)
    (ξ : (parameter.obj k).obj (op n)) (i : Fin (n.len + 1)) :
    (SSet.opObjEquiv ((daggerParameter.obj k).dagger.app (op n) ξ)).obj i =
      ξ.obj i.rev := rfl

/-- The reversed arrow is the inverse of the original reversed arrow. -/
theorem reversal_arrows (k n : SimplexCategory)
    (ξ : (parameter.obj k).obj (op n)) {i j : Fin (n.len + 1)} (f : i ⟶ j) :
    (SSet.opObjEquiv ((daggerParameter.obj k).dagger.app (op n) ξ)).map f =
      Groupoid.inv (((DaggerOriginalNerveOppositeMap.reverseDiagram ξ).map f).unop) := rfl

end

end DaggerModels.PartII.GroupoidSimplexReversal
