import DaggerModelsPartII.LocalPushout
import DaggerModelsPartII.LocalEquivalenceClasses

/-!
# Cobase change of local trivial cofibrations

The generic derived mapping-space pushout theorem implies cobase-change
stability for the intersection of the original cofibrations with the local
equivalences of any specified family.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII.Localization

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, v} C]

/-- In a left proper model category, cofibrations that are local equivalences
are stable under cobase change, for any localizing family.  The model
structure after localization is not assumed to exist. -/
theorem localTrivialCofibrations_cobaseChange
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D}
      {l : B ⟶ P} {r : D ⟶ P}, IsPushout i k l r →
        cofibrations C i → weakEquivalences C k → weakEquivalences C l)
    (S : MorphismProperty C) :
    (cofibrations C ⊓ localEquivalences S).IsStableUnderCobaseChange where
  of_isPushout sq hi := by
    refine ⟨(cofibrations C).of_isPushout sq hi.1, ?_⟩
    intro Z hZ
    letI : IsFibrant Z := hZ.1
    exact homotopyMappingWeakEquivalences_of_pushout leftProper sq.flip hi.1 Z
      (hi.2 Z hZ)

end

end DaggerModels.PartII.Localization
