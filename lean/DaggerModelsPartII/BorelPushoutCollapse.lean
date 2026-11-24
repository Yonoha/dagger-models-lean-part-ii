import DaggerModelsPartII.BorelInvariantSplit
import DaggerModelsPartII.BorelDiscreteOrbitsModel
import DaggerModelsPartII.KanLeftProper
import DaggerModelsPartII.InvariantOrbitSets

/-!
# The pushout collapse of a discrete Borel construction

Replacing the invariant-subset summand by its strict orbit set leaves only
the Borel construction on the complement. If all fixed elements lie in the
subset, the remaining collapse is a weak equivalence.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.BorelDiscreteOrbits

open DaggerModels.FreeInvolution InvariantDiagonalOrbits DiscreteOrbitSubobject

noncomputable section

variable (E : SSet.{u}) (σ : E ≅ E) (hσ : σ.hom ≫ σ.hom = 𝟙 E)
  {X : Type u} (τ : X ≃ X) (hτ : Function.Involutive τ)
  (A : Set X) (hA : ∀ x ∈ A, τ x ∈ A)

abbrev subsetOrbitObject : SSet.{u} := (SimplicialObject.const (Type u)).obj
  (Orbit (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA))
abbrev complementOrbitObject : SSet.{u} := (SimplicialObject.const (Type u)).obj
  (Orbit (complementInvolution τ hτ A hA) (complementInvolutive τ hτ A hA))

/-- Collapse of the subset Borel construction to its own strict orbit object. -/
abbrev subsetCollapse := collapse E σ hσ
  (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA)

/-- Collapse of the complementary Borel construction. -/
abbrev complementCollapse := collapse E σ hσ
  (complementInvolution τ hτ A hA) (complementInvolutive τ hτ A hA)

/-- The manuscript's pushout before its final collapse. -/
def collapsedPushout : SSet.{u} := pushout
  (subsetBorelInclusion E σ hσ τ hτ A hA) (subsetCollapse E σ hσ τ hτ A hA)

/-- Collapse the subset summand and retain the complement summand. -/
def splitPushoutMap : borel E σ hσ τ hτ ⟶
    (subsetOrbitObject τ hτ A hA ⨿ complementBorel E σ hσ τ hτ A hA) :=
  splitDesc E σ hσ τ hτ A hA
    (subsetCollapse E σ hσ τ hτ A hA ≫ coprod.inl) coprod.inr

/-- The explicit split object is the same pushout, with the original maps retained. -/
theorem splitPushout_isPushout : IsPushout
    (subsetBorelInclusion E σ hσ τ hτ A hA) (subsetCollapse E σ hσ τ hτ A hA)
    (splitPushoutMap E σ hσ τ hτ A hA) coprod.inl := by
  let e := splitCoproductIso E σ hσ τ hτ A hA
  apply (IsPushout.of_coprod_inl_with_id (subsetCollapse E σ hσ τ hτ A hA)
    (complementBorel E σ hσ τ hτ A hA)).of_iso
    (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  · simp [e]
  · simp
  · apply coprod.hom_ext <;>
      simp [e, splitPushoutMap]
  · simp

/-- The split presentation of the actual categorical pushout. -/
def splitPushoutIso : collapsedPushout E σ hσ τ hτ A hA ≅
    (subsetOrbitObject τ hτ A hA ⨿ complementBorel E σ hσ τ hτ A hA) :=
  (splitPushout_isPushout E σ hσ τ hτ A hA).isoPushout.symm

@[reassoc (attr := simp)] theorem inl_splitPushoutIso :
    pushout.inl _ _ ≫ (splitPushoutIso E σ hσ τ hτ A hA).hom =
      splitPushoutMap E σ hσ τ hτ A hA :=
  (splitPushout_isPushout E σ hσ τ hτ A hA).inl_isoPushout_inv

@[reassoc (attr := simp)] theorem inr_splitPushoutIso :
    pushout.inr _ _ ≫ (splitPushoutIso E σ hσ τ hτ A hA).hom = coprod.inl :=
  (splitPushout_isPushout E σ hσ τ hτ A hA).inr_isoPushout_inv

/-- Collapse the remaining complement, with separate orbit coordinates for the two pieces. -/
def splitCollapse : collapsedPushout E σ hσ τ hτ A hA ⟶
    (subsetOrbitObject τ hτ A hA ⨿ complementOrbitObject τ hτ A hA) :=
  (splitPushoutIso E σ hσ τ hτ A hA).hom ≫
    coprod.map (𝟙 _) (complementCollapse E σ hσ τ hτ A hA)

/-- Adjoining a fixed summand preserves ordinary Kan weak equivalences. -/
theorem coprod_id_weak {B D : SSet.{u}} (p : B ⟶ D) (T : SSet.{u})
    (hp : weakEquivalences SSet.{u} p) :
    weakEquivalences SSet.{u} (coprod.map (𝟙 T) p) := by
  have hw : weakEquivalences SSet.{u} (coprod.map p (𝟙 T)) :=
    kanLeftProper (IsPushout.of_coprod_inl_with_id p T)
      ((cofibration_iff _).mp inferInstance) hp
  have heq : coprod.map (𝟙 T) p =
      (coprod.braiding T B).hom ≫ coprod.map p (𝟙 T) ≫ (coprod.braiding D T).hom := by
    apply coprod.hom_ext <;> simp
  haveI : WeakEquivalence (coprod.map p (𝟙 T)) := (weakEquivalence_iff _).mpr hw
  rw [heq]
  exact (weakEquivalence_iff _).mp inferInstance

/-- If the invariant subset contains every fixed element, the pushout collapse
in the split orbit presentation is a Kan weak equivalence. -/
theorem splitCollapse_weak (hfixed : ∀ x, τ x = x → x ∈ A)
    (hE : trivialFibrations SSet.{u} (terminal.from E)) :
    weakEquivalences SSet.{u} (splitCollapse E σ hσ τ hτ A hA) := by
  have hfree : ∀ x, complementInvolution τ hτ A hA x ≠ x := by
    intro x hx
    exact complement_free τ A hfixed x (congrArg Subtype.val hx)
  have hp := collapse_trivialFibration E σ hσ
    (complementInvolution τ hτ A hA) (complementInvolutive τ hτ A hA) hfree hE
  have hw := coprod_id_weak (complementCollapse E σ hσ τ hτ A hA)
    (subsetOrbitObject τ hτ A hA) hp.2
  haveI : WeakEquivalence
      (coprod.map (𝟙 (subsetOrbitObject τ hτ A hA))
        (complementCollapse E σ hσ τ hτ A hA)) := (weakEquivalence_iff _).mpr hw
  exact (weakEquivalence_iff _).mp (inferInstance : WeakEquivalence
    ((splitPushoutIso E σ hσ τ hτ A hA).hom ≫
      coprod.map (𝟙 _) (complementCollapse E σ hσ τ hτ A hA)))

@[reassoc (attr := simp)] theorem subsetInclusion_collapse :
    subsetBorelInclusion E σ hσ τ hτ A hA ≫ collapse E σ hσ τ hτ =
      subsetCollapse E σ hσ τ hτ A hA ≫
        InvariantOrbitSets.subsetConstantInclusion τ hτ A hA := by
  apply NatTrans.ext
  funext n q
  induction q using Quotient.inductionOn with
  | _ p => rfl

@[reassoc (attr := simp)] theorem complementInclusion_collapse :
    complementBorelInclusion E σ hσ τ hτ A hA ≫ collapse E σ hσ τ hτ =
      complementCollapse E σ hσ τ hτ A hA ≫
        InvariantOrbitSets.complementConstantInclusion τ hτ A hA := by
  apply NatTrans.ext
  funext n q
  induction q using Quotient.inductionOn with
  | _ p => rfl

/-- The canonical collapse from the pushout to the full strict orbit object. -/
def pushoutCollapse : collapsedPushout E σ hσ τ hτ A hA ⟶
    (SimplicialObject.const (Type u)).obj (Orbit τ hτ) :=
  pushout.desc (collapse E σ hσ τ hτ)
    (InvariantOrbitSets.subsetConstantInclusion τ hτ A hA)
    (subsetInclusion_collapse E σ hσ τ hτ A hA)

/-- The canonical pushout collapse is exactly the split collapse followed by
the full orbit coproduct comparison. -/
theorem splitCollapse_factor :
    splitCollapse E σ hσ τ hτ A hA ≫
      (InvariantOrbitSets.constantOrbitCoproductIso τ hτ A hA).hom =
        pushoutCollapse E σ hσ τ hτ A hA := by
  apply pushout.hom_ext
  · simp only [splitCollapse, Category.assoc, inl_splitPushoutIso_assoc,
      pushoutCollapse, pushout.inl_desc]
    apply (splitIsColimit E σ hσ τ hτ A hA).hom_ext
    rintro ⟨(_ | _)⟩ <;> simp [splitPushoutMap, Category.assoc]
  · simp [splitCollapse, pushoutCollapse, Category.assoc]

/-- The pointwise Borel pushout collapse is a Kan weak equivalence when all
fixed elements lie in the invariant subset. -/
theorem pushoutCollapse_weak (hfixed : ∀ x, τ x = x → x ∈ A)
    (hE : trivialFibrations SSet.{u} (terminal.from E)) :
    weakEquivalences SSet.{u} (pushoutCollapse E σ hσ τ hτ A hA) := by
  haveI : WeakEquivalence (splitCollapse E σ hσ τ hτ A hA) :=
    (weakEquivalence_iff _).mpr (splitCollapse_weak E σ hσ τ hτ A hA hfixed hE)
  rw [← splitCollapse_factor]
  exact (weakEquivalence_iff _).mp inferInstance

/-- The manuscript's actual `EC₂` gives a weak pushout collapse for every
invariant subset containing all fixed elements. -/
theorem actualEC2_pushoutCollapse_weak
    (hfixed : ∀ x, τ x = x → x ∈ A) :
    weakEquivalences SSet.{u}
      (pushoutCollapse DaggerOriginalEC2SimplicialAction.simplicialEC2
        ec2Involution ec2Involution_square τ hτ A hA) := by
  apply pushoutCollapse_weak _ _ _ _ _ _ _ hfixed
  haveI : Nonempty DaggerOriginalDaggerRealizationC2Action.C2.{u} := ⟨1⟩
  exact DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration
    (terminal.from DaggerOriginalEC2SimplicialAction.simplicialEC2) terminalIsTerminal

end

end DaggerModels.PartII.BorelDiscreteOrbits
