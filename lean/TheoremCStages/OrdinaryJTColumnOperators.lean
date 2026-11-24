import OrdinaryJTCurriedAdjunction
import OrdinaryJTNativeRightNerveReedy

/-!
# Scalar operators of the actual ordinary JT right-nerve columns

Both directions are the original restricted-Yoneda precomposition maps.
The checked curry coordinate lemmas expose the literal tensor-weight maps
before any internal-Hom comparison is made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels
open scoped Prod

namespace DaggerModels.PartII.OrdinaryJTColumnOperators

noncomputable section

private abbrev R (X : SSet.{0}) := OrdinaryJTCurriedAdjunction.right.obj X
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k

/-- The actual horizontal operator precomposes the original first tensor
factor. -/
theorem column_horizontal_map_down (X : SSet.{0})
    (k : SimplexCategory) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) (z : ((R X).flip.obj (op k)).obj m) :
    (((R X).flip.obj (op k)).map f z).down =
      (SSet.stdSimplex.map f.unop ▷ J k) ≫ z.down := by
  have hmap : ((R X).flip.obj (op k)).map f =
      (OrdinaryJTRealization.nerve.obj X).map (f.unop ×ₘ 𝟙 k).op :=
    OrdinaryJTNativeRightNerveReedy.nativeSpace_map_app X f.unop k
  rw [hmap]
  simp only [OrdinaryJTRealization.nerve,
    Presheaf.restrictedULiftYoneda_obj_map, uliftYoneda_obj_map_down,
    Quiver.Hom.unop_op]
  rw [OrdinaryJTRealization.tFunctor_map,
    GroupoidSimplex.parameter.map_id, MonoidalCategory.tensorHom_id]

/-- The actual vertical operator precomposes the original second tensor
factor. -/
theorem column_parameter_map_down (X : SSet.{0})
    {k l : SimplexCategory} (θ : k ⟶ l)
    (m : SimplexCategoryᵒᵖ)
    (z : ((R X).flip.obj (op l)).obj m) :
    (((R X).flip.map θ.op).app m z).down =
      (SSet.stdSimplex.obj m.unop ◁ GroupoidSimplex.parameter.map θ) ≫ z.down := by
  have hmap : ((R X).flip.map θ.op).app m =
      (OrdinaryJTRealization.nerve.obj X).map (𝟙 m.unop ×ₘ θ).op :=
    JTRealizationDiagonal.ordinaryCurry_obj_obj_map
      (OrdinaryJTRealization.nerve.obj X) m.unop θ
  rw [hmap]
  simp only [OrdinaryJTRealization.nerve,
    Presheaf.restrictedULiftYoneda_obj_map, uliftYoneda_obj_map_down,
    Quiver.Hom.unop_op]
  rw [OrdinaryJTRealization.tFunctor_map]
  have hm : SSet.stdSimplex.map (𝟙 m.unop) = 𝟙 (SSet.stdSimplex.obj m.unop) :=
    SSet.stdSimplex.map_id m.unop
  rw [hm, MonoidalCategory.id_tensorHom]

#print axioms column_horizontal_map_down
#print axioms column_parameter_map_down

end
end DaggerModels.PartII.OrdinaryJTColumnOperators
