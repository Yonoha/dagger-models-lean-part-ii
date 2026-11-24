import DaggerModelsPartII.BorelDiscreteOrbits
import OriginalCodiscreteNerveInjective
import OriginalEC2SimplicialAction

/-!
# The Borel collapse for a free discrete factor

Projection from a family of copies of an injective simplicial set is a
trivial Kan fibration. Applied to the actual codiscrete nerve `EC₂`, this
proves the pointwise collapse for every free discrete involution.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.BorelDiscreteOrbits

noncomputable section

variable (E : SSet.{u})

/-- Projection from a family of copies to its second factor. -/
def copiesSecond (T : Type u) : copies E T ⟶ E where
  app _ := Prod.snd
  naturality _ _ _ := rfl

/-- A family projection is a trivial fibration whenever the simplicial
factor's terminal projection is a trivial fibration. -/
theorem copiesProjection_trivialFibration (T : Type u)
    (hE : trivialFibrations SSet.{u} (terminal.from E)) :
    trivialFibrations SSet.{u} (copiesProjection E T) := by
  rw [← cofibrations_rlp]
  intro A B i hi
  have hl : HasLiftingProperty i (terminal.from E) :=
    hasLiftingProperty_of_wfs i (terminal.from E) hi hE
  constructor
  intro f g sq
  let sqE : CommSq (f ≫ copiesSecond E T) i (terminal.from E) (terminal.from B) :=
    ⟨terminal.hom_ext _ _⟩
  letI := hl
  let l := sqE.lift
  let lift : B ⟶ copies E T := {
    app := fun n b ↦ (g.app n b, l.app n b)
    naturality := by
      intro n m α
      funext b
      apply Prod.ext
      · exact congrFun (g.naturality α) b
      · exact congrFun (l.naturality α) b }
  refine CommSq.HasLift.mk' ⟨lift, ?_, ?_⟩
  · apply NatTrans.ext
    funext n a
    apply Prod.ext
    · exact (congrFun (congr_app sq.w n) a).symm
    · exact congrFun (congr_app sqE.fac_left n) a
  · rfl

variable (σ : E ≅ E) (hσ : σ.hom ≫ σ.hom = 𝟙 E)
  {X : Type u} (τ : X ≃ X) (hτ : Function.Involutive τ)

/-- For a free discrete involution, the Borel collapse is a trivial Kan fibration. -/
theorem collapse_trivialFibration (hfree : ∀ x, τ x ≠ x)
    (hE : trivialFibrations SSet.{u} (terminal.from E)) :
    trivialFibrations SSet.{u} (collapse E σ hσ τ hτ) := by
  have ht := copiesProjection_trivialFibration E (DaggerModels.FreeInvolution.Orbit τ hτ) hE
  haveI : Fibration (copiesProjection E (DaggerModels.FreeInvolution.Orbit τ hτ)) :=
    (mem_trivialFibrations_iff _).mp ht |>.1
  haveI : WeakEquivalence (copiesProjection E (DaggerModels.FreeInvolution.Orbit τ hτ)) :=
    (mem_trivialFibrations_iff _).mp ht |>.2
  rw [← cancellationIso_collapse E σ hσ τ hτ hfree]
  exact mem_trivialFibrations _

open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction

/-- The actual generator action on the original simplicial `EC₂`. -/
def ec2Involution : simplicialEC2.{u} ≅ simplicialEC2.{u} :=
  simplicialAction.ρAut generator

theorem ec2Involution_square :
    ec2Involution.{u}.hom ≫ ec2Involution.hom = 𝟙 simplicialEC2 := by
  have hg : generator.{u} * generator = (1 : C2.{u}) := by decide
  change simplicialAction.ρ generator ≫ simplicialAction.ρ generator = 𝟙 _
  rw [← End.mul_def, ← map_mul, hg, Action.ρ_one]

/-- The pointwise Borel collapse for the manuscript's actual `EC₂`. -/
theorem actualEC2_collapse_trivialFibration (hfree : ∀ x, τ x ≠ x) :
    trivialFibrations SSet.{u}
      (collapse simplicialEC2 ec2Involution ec2Involution_square τ hτ) := by
  apply collapse_trivialFibration _ _ _ _ _ hfree
  haveI : Nonempty C2.{u} := ⟨1⟩
  exact DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration
    (terminal.from simplicialEC2) terminalIsTerminal

end

end DaggerModels.PartII.BorelDiscreteOrbits
