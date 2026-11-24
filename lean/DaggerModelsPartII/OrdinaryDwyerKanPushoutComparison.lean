import DaggerModelsPartII.WeakCofibrationCobase
import DaggerModelsPartII.WeakCofibrationPushoutComparison
import DaggerModelsPartII.JTOrdinaryEssentialSurjCobase
import DaggerModelsPartII.OrdinaryDwyerKanClosure
import DaggerModelsPartII.OrdinaryBergnerGenerators

/-!
# Full ordinary DK comparison of actual pushout squares

The existing original ordinary first weak factorization system and the proved
local-cobase and component-essential-surjectivity results supply the generic
weak-cofibration gluing theorem. No ordinary model or second weak factorization
system is introduced. All four faces of the supplied comparison cube remain
part of the theorem, with the original endpoints and actual pushout apex maps.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty DaggerModels
open DaggerOrdinaryRigidificationCof DaggerModels.OrdinaryDwyerKanCore

universe u

namespace DaggerModels.OrdinaryDwyerKanPushoutComparison

noncomputable section

private local instance : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits

private local instance : ordinaryCofibrations.{u}.IsStableUnderComposition := by
  dsimp [ordinaryCofibrations]
  infer_instance

private local instance : ordinaryCofibrations.{u}.IsStableUnderCobaseChange := by
  dsimp [ordinaryCofibrations]
  infer_instance

/-- The retained original ordinary cofibration/trivial-fibration factorization
comes from the already proved literal boundary/object small object argument. -/
theorem ordinary_hasFactorization :
    ordinaryCofibrations.{u}.HasFactorization ordinaryTrivialFibrations.{u} := by
  rw [ordinaryCofibrations,
    ← OrdinaryBergnerGenerators.generators_rlp_eq_ordinaryTrivialFibrations]
  letI := OrdinaryBergnerGenerators.generators_hasSmallObjectArgument.{u}
  infer_instance

private local instance :
    ordinaryCofibrations.{u}.HasFactorization ordinaryTrivialFibrations.{u} :=
  ordinary_hasFactorization

/-- The original ordinary trivial-fibration class satisfies the unchanged
ordinary DK predicate on the same Hom maps and component objects. -/
theorem ordinaryTrivialFibrations_le_W : ordinaryTrivialFibrations.{u} ≤ W.{u} := by
  intro C D p hp
  refine ⟨fun x y ↦ (hp.2 x y).2, ?_⟩
  apply Functor.essSurj_of_surj
  exact hp.1

/-- Actual ordinary DK equivalences are left proper along the original
ordinary cofibration class. -/
theorem leftProper
    {A B D P : SimplicialCat.{u, u}}
    {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    (sq : IsPushout i k l r) (hi : ordinaryCofibrations i) (hk : W k) : W l :=
  OrdinaryEssentialSurjCobase.weak_of_isPushout_along_cofibration k i r l sq.flip hi hk

/-- Every weak original ordinary cofibration stays weak under arbitrary
cobase change; the arbitrary attaching leg is factored, not assumed cofibrant. -/
def weakCofibrations_stableUnderCobaseChange :
    (ordinaryCofibrations.{u} ⊓ W.{u}).IsStableUnderCobaseChange :=
  PartII.WeakCofibrationCobase.stableUnderCobaseChange
    ordinaryCofibrations W ordinaryTrivialFibrations ordinaryTrivialFibrations_le_W
    (fun sq hi hk ↦ leftProper sq hi hk)

private local instance :
    (ordinaryCofibrations.{u} ⊓ W.{u}).IsStableUnderCobaseChange :=
  weakCofibrations_stableUnderCobaseChange

/-- A comparison of actual ordinary pushouts is DK when all three original
span components are DK and the corresponding attachment legs are cofibrations. -/
theorem weak_of_pushoutComparison
    {A B D P A' B' D' P' : SimplicialCat.{u, u}}
    {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    {i' : A' ⟶ B'} {k' : A' ⟶ D'} {l' : B' ⟶ P'} {r' : D' ⟶ P'}
    (sq : IsPushout i k l r) (sq' : IsPushout i' k' l' r')
    (hi : ordinaryCofibrations i) (hi' : ordinaryCofibrations i')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') (d : P ⟶ P')
    (h₁ : i ≫ b = a ≫ i') (h₂ : k ≫ c = a ≫ k')
    (h₃ : l ≫ d = b ≫ l') (h₄ : r ≫ d = c ≫ r')
    (ha : W a) (hb : W b) (hc : W c) : W d :=
  PartII.WeakCofibrationPushoutComparison.weak_of_pushoutComparison
    (Cof := ordinaryCofibrations) (W := W) (TF := ordinaryTrivialFibrations)
    ordinaryTrivialFibrations_le_W (fun sq hi hk ↦ leftProper sq hi hk)
    sq sq' hi hi' a b c d h₁ h₂ h₃ h₄ ha hb hc

end

end DaggerModels.OrdinaryDwyerKanPushoutComparison
