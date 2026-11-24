import DaggerModelsPartII.ResolutionAdjunction
import DaggerModels.FreeDagger
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Finite presentability of the coefficient and outer parameters of the external tensor. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII

attribute [local instance] Cardinal.fact_isRegular_aleph0

local instance tensorPresentabilityColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits

/-- The free dagger functor sends a finitely presentable simplicial set to a finitely
presentable coefficient, since its right adjoint preserves colimits. -/
theorem freeDagger_obj_isFinitelyPresentable (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} (DaggerModels.freeDagger.obj K) := by
  letI := DaggerSSet.forget_preservesColimits.{u}
  letI : DaggerSSet.forget.{u}.IsCardinalAccessible Cardinal.aleph0.{u} :=
    (Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize).mpr inferInstance
  exact DaggerModels.freeDaggerAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 K

/-- The external tensor of finitely presentable objects in both variables is finitely presentable. -/
theorem externalTensor_obj_isFinitelyPresentable (A : DaggerSSet.{u}) (K : SSet.{u})
    [IsFinitelyPresentable.{u} A] [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} ((externalTensor A).obj K) := by
  letI : (mappingSimplicialSet A).IsCardinalAccessible Cardinal.aleph0.{u} := by
    constructor
    intro J _ _
    letI : PreservesColimitsOfShape J (coyoneda.obj (op A)) :=
      preservesColimitsOfShape_of_isCardinalPresentable A Cardinal.aleph0 J
    change PreservesColimitsOfShape J ((Functor.whiskeringRight _ _ _).obj (coyoneda.obj (op A)))
    exact CategoryTheory.whiskeringRight_preservesColimitsOfShape _
  exact (externalTensorAdjunction A).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 K

end DaggerModels.PartII
