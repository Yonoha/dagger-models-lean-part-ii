import DaggerModelsPartII.ReedyFactorizationProperties
import DaggerModelsPartII.ReedyLifting
import DaggerModelsPartII.RelativeArrows
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-! Weak factorization systems on simplicial objects from relative Reedy maps. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Opposite

universe v u

namespace DaggerModels.PartII

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

/-- The class with all relative latching maps in the coefficient class (P). -/
def reedyLatchingProperty (P : MorphismProperty C) :
    MorphismProperty (SimplexCategoryᵒᵖ ⥤ C) :=
  fun _ _ f ↦ ∀ n : ℕ, P (relativeLatchingMap n f)

/-- The class with all relative matching maps in the coefficient class (Q). -/
def reedyMatchingProperty (Q : MorphismProperty C) :
    MorphismProperty (SimplexCategoryᵒᵖ ⥤ C) :=
  fun _ _ f ↦ ∀ n : ℕ, Q (relativeMatchingMap n f)

instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    (reedyLatchingProperty P).IsStableUnderRetracts where
  of_retract h hf n :=
    MorphismProperty.of_retract (P := P)
      (CategoryTheory.Retract.map h (relativeLatchingArrows (latchingComparison n))) (hf n)

instance (Q : MorphismProperty C) [Q.IsStableUnderRetracts] :
    (reedyMatchingProperty Q).IsStableUnderRetracts where
  of_retract h hf n :=
    MorphismProperty.of_retract (P := Q)
      (CategoryTheory.Retract.map h (relativeMatchingArrows (matchingComparison n))) (hf n)

instance (P Q : MorphismProperty C) [HasFactorization P Q] :
    HasFactorization (reedyLatchingProperty P) (reedyMatchingProperty Q) where
  nonempty_mapFactorizationData f := ⟨{
    Z := reedyFactorizationMid f P Q
    i := reedyFactorizationLeft f P Q
    p := reedyFactorizationRight f P Q
    fac := reedyFactorization_fac f P Q
    hi := reedyFactorizationLeft_relative_mem f P Q
    hp := reedyFactorizationRight_relative_mem f P Q }⟩

/-- A coefficient weak factorization system induces one via relative Reedy maps. -/
theorem reedyRelativeWeakFactorizationSystem (P Q : MorphismProperty C)
    [IsWeakFactorizationSystem P Q] :
    IsWeakFactorizationSystem (reedyLatchingProperty P) (reedyMatchingProperty Q) := by
  letI : P.IsStableUnderRetracts := by
    rw [← llp_eq_of_wfs P Q]
    infer_instance
  letI : Q.IsStableUnderRetracts := by
    rw [← rlp_eq_of_wfs P Q]
    infer_instance
  apply IsWeakFactorizationSystem.mk'
  intro A B X Y i p hi hp
  exact reedyLiftingOfRelativeMaps (fun n ↦ hasLiftingProperty_of_wfs
    (W₁ := P) (W₂ := Q) (relativeLatchingMap n i) (relativeMatchingMap n p) (hi n) (hp n))

end DaggerModels.PartII
