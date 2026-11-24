import DaggerModelsPartII.JTFreeInnerReplacement
import NativeInnerHornFactorization

/-!
# Functorial free-inner replacement for dagger simplicial sets

The literal free dagger inner horns form a small generating family. The locally
presentable small-object argument factors every dagger map into the associated
left and right classes. The terminal-map factorization is functorial, its left
factor is an original dagger Joyal trivial cofibration, and its target has an
underlying quasi-category. Vertex preservation is a separate statement.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra DaggerModels

universe u

namespace DaggerModels.PartII.JTFreeInnerFactorization

noncomputable section

private local instance : ModelCategory DaggerSSet.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}

private local instance : IsLocallyPresentable.{u} DaggerSSet.{u} :=
  daggerSSetLocallyPresentable.{u}

private local instance : PreservesLimits DaggerSSet.forget.{u} :=
  DaggerSSet.forget_preservesLimits

/-- The small family of literal free dagger inner-horn inclusions. -/
def generators : MorphismProperty DaggerSSet.{u} :=
  ofHoms JTFreeInnerReplacement.generator

/-- The exact lifting class tested against every literal free dagger inner horn. -/
def innerFibrations : MorphismProperty DaggerSSet.{u} := generators.rlp

/-- The corresponding small-object left class. -/
def innerAnodyne : MorphismProperty DaggerSSet.{u} := generators.rlp.llp

instance generatorsSmall : IsSmall.{u} generators.{u} := isSmall_ofHoms _

private instance generatorsSmallObject : HasSmallObjectArgument.{u} generators.{u} :=
  DaggerSmithSolutionSet.smallObjectArgument generators

/-- The generic locally presentable small-object factorization of actual dagger maps. -/
def factorization : innerAnodyne.{u}.FunctorialFactorizationData innerFibrations.{u} :=
  DaggerSmithSolutionSet.soaFactorization generators

/-- The right class is created by the actual free dagger adjunction. -/
theorem innerFibrations_iff_underlying {X Y : DaggerSSet.{u}} (p : X ⟶ Y) :
    innerFibrations p ↔ DaggerNativeInnerHornFactorization.innerFibrations p.hom := by
  constructor
  · intro hp A B i hi
    obtain ⟨a⟩ := hi
    exact (freeDaggerAdjunction.hasLiftingProperty_iff _ p).1 (hp _ ⟨a⟩)
  · intro hp A B i hi
    obtain ⟨a⟩ := hi
    exact (freeDaggerAdjunction.hasLiftingProperty_iff _ p).2 (hp _ ⟨a⟩)

/-- Every generator belongs to the exact original trivial-cofibration class. -/
theorem generators_le_original_trivial :
    generators.{u} ≤ trivialCofibrations DaggerSSet.{u} := by
  intro X Y f hf
  obtain ⟨a⟩ := hf
  exact JTFreeInnerReplacement.generator_trivialCofibration a

/-- The whole small-object left class is original trivial cofibrant. -/
theorem innerAnodyne_le_original_trivial :
    innerAnodyne.{u} ≤ trivialCofibrations DaggerSSet.{u} := by
  have h := antitone_llp (antitone_rlp generators_le_original_trivial.{u})
  rw [rlp_eq_of_wfs (trivialCofibrations DaggerSSet.{u}) (fibrations DaggerSSet.{u}),
    llp_eq_of_wfs (trivialCofibrations DaggerSSet.{u}) (fibrations DaggerSSet.{u})] at h
  exact h

/-- Regard every terminal map as an arrow, naturally in its source. -/
def terminalArrow : DaggerSSet.{u} ⥤ Arrow DaggerSSet.{u} where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (terminalIsTerminal.hom_ext _ _)
  map_id _ := by apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply Arrow.hom_ext <;> simp

/-- Functorial free-inner replacement in the actual dagger category. -/
def replacement : DaggerSSet.{u} ⥤ DaggerSSet.{u} :=
  terminalArrow ⋙ factorization.Z

/-- The natural map to the free-inner replacement. -/
def unit : 𝟭 DaggerSSet.{u} ⟶ replacement.{u} where
  app X := factorization.i.app (terminalArrow.obj X)
  naturality _X _Y f := factorization.i.naturality (terminalArrow.map f)

/-- The right factor fills all underlying native inner horns. -/
theorem replacement_underlying_quasicategory (X : DaggerSSet.{u}) :
    (replacement.obj X).toSSet.Quasicategory := by
  have hT := Limits.IsTerminal.isTerminalObj DaggerSSet.forget _ terminalIsTerminal
  exact (DaggerNativeInnerHornFactorization.quasicategory_iff_inner_terminal
    (factorization.p.app (terminalArrow.obj X)).hom hT).2
      ((innerFibrations_iff_underlying _).1 (factorization.hp _))

/-- The unit is the left factor of the literal terminal-map factorization. -/
theorem unit_innerAnodyne (X : DaggerSSet.{u}) : innerAnodyne (unit.app X) :=
  factorization.hi _

/-- The unit is an original dagger Joyal trivial cofibration. -/
theorem unit_trivialCofibration (X : DaggerSSet.{u}) :
    trivialCofibrations DaggerSSet.{u} (unit.app X) :=
  innerAnodyne_le_original_trivial _ (unit_innerAnodyne X)

end

end DaggerModels.PartII.JTFreeInnerFactorization
