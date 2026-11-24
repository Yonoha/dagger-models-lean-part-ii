import DaggerModelsPartII.CobaseFunctorColimits
import DaggerModelsPartII.ReducedCylinder

/-!
# Colimit preservation for the actual reduced-cylinder under-functor

Both tensor functors preserve colimits by the existing internal-Hom
adjunction. The fixed-boundary cobase universal property then proves
colimit preservation in the undercategory, including degree-zero empty
latching diagrams and disconnected positive-degree diagrams.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MonoidalClosed

universe u

namespace DaggerModels.PartII.ReducedCylinder

noncomputable section

private instance boundaryTensor_preservesColimits (A : SSet.{u}) :
    PreservesColimitsOfSize.{0, 0} (boundaryTensor A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

private instance intervalTensor_preservesColimits (B : SSet.{u}) :
    PreservesColimitsOfSize.{0, 0} (intervalTensor B) :=
  (ihom.adjunction B).leftAdjoint_preservesColimits

/-- The literal reduced-cylinder functor preserves all small colimits
needed for the actual Reedy latching diagrams, including the empty one. -/
instance functor_preservesColimits {A B : SSet.{u}} (j : A ⟶ B) :
    PreservesColimitsOfSize.{0, 0} (functor j) where
  preservesColimitsOfShape := by
    intro J _
    constructor
    intro K
    exact CobaseFunctorColimits.preservesColimit (tensorInclusion j) A
      (tensorProjection A) (functor j) (left j) (fun K ↦ functor_isPushout j (K := K))

end

end DaggerModels.PartII.ReducedCylinder
