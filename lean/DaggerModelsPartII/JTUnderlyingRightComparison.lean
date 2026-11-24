import DaggerModelsPartII.DaggerJTAdjunction

/-!
# Forgetting dagger in the original JT right adjoint

The strict equality of the two underlying left realizations gives the
manuscript's natural comparison of right adjoints. Its adjunction compatibility
is an equality for the actual functors. No invertibility or fiber statement is
asserted here.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels

namespace DaggerModels.PartII.JTUnderlyingRightComparison

open DaggerJTRealization DaggerJTAdjunction JTReversalInput OrdinaryJTRealization

noncomputable section

/-- The underlying ordinary adjoint of the actual dagger counit. -/
def comparisonComponent (X : DaggerSSet.{0}) :
    ordinaryInput.obj (daggerNerve.obj X) ⟶ nerve.obj (DaggerSSet.forget.obj X) :=
  realizationNerveAdjunction.homEquiv _ _
    (DaggerSSet.forget.map (adjunction.counit.app X))

/-- The comparison is natural in the original dagger simplicial set. -/
theorem comparisonComponent_naturality {X Y : DaggerSSet.{0}} (f : X ⟶ Y) :
    ordinaryInput.map (daggerNerve.map f) ≫ comparisonComponent Y =
      comparisonComponent X ≫ nerve.map (DaggerSSet.forget.map f) := by
  rw [comparisonComponent, comparisonComponent,
    ← realizationNerveAdjunction.homEquiv_naturality_left,
    ← realizationNerveAdjunction.homEquiv_naturality_right]
  apply congrArg (realizationNerveAdjunction.homEquiv _ _)
  change DaggerSSet.forget.map
      (daggerRealization.map (daggerNerve.map f)) ≫
        DaggerSSet.forget.map (adjunction.counit.app Y) = _
  rw [← DaggerSSet.forget.map_comp, ← DaggerSSet.forget.map_comp]
  exact congrArg DaggerSSet.forget.map (adjunction.counit.naturality f)

/-- The actual natural comparison after forgetting the dagger. -/
def comparison : daggerNerve ⋙ ordinaryInput ⟶ DaggerSSet.forget ⋙ nerve where
  app := comparisonComponent
  naturality _ _ f := comparisonComponent_naturality f

/-- The two original adjunction bijections commute with forgetting dagger. -/
theorem homEquiv_comparison (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (X : DaggerSSet.{0}) (f : daggerRealization.obj W ⟶ X) :
    ordinaryInput.map (adjunction.homEquiv W X f) ≫ comparison.app X =
      realizationNerveAdjunction.homEquiv _ _ (DaggerSSet.forget.map f) := by
  change ordinaryInput.map (adjunction.homEquiv W X f) ≫ comparisonComponent X = _
  rw [comparisonComponent, ← realizationNerveAdjunction.homEquiv_naturality_left]
  apply congrArg (realizationNerveAdjunction.homEquiv _ _)
  change DaggerSSet.forget.map
      (daggerRealization.map (adjunction.homEquiv W X f)) ≫
        DaggerSSet.forget.map (adjunction.counit.app X) = DaggerSSet.forget.map f
  rw [← DaggerSSet.forget.map_comp]
  exact congrArg DaggerSSet.forget.map
    ((adjunction.homEquiv W X).symm_apply_apply f)

/-- The manuscript's two-step underlying transpose uses the same natural
comparison, with the target map retained explicitly. -/
theorem homEquiv_composite_comparison (W : SegalLocalizers.ReverseDaggerSpace.{0})
    {T X : DaggerSSet.{0}} (g : daggerRealization.obj W ⟶ T) (e : T ⟶ X) :
    ordinaryInput.map (adjunction.homEquiv W X (g ≫ e)) ≫ comparison.app X =
      realizationNerveAdjunction.homEquiv _ _ (DaggerSSet.forget.map g) ≫
        nerve.map (DaggerSSet.forget.map e) := by
  rw [homEquiv_comparison, DaggerSSet.forget.map_comp,
    realizationNerveAdjunction.homEquiv_naturality_right]

end

end DaggerModels.PartII.JTUnderlyingRightComparison
