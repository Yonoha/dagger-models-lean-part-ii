import DaggerModelsPartII.InjectiveKanDiagramClasses
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.CategoryTheory.Generator.Basic

/-! Small test families of monomorphisms for injective Kan diagrams.

Subobjects of free representables alone do not generate all injective monomorphisms:
for a group action, every free orbit stays free under their pushouts. The second
family also allows quotients of free representables, so stabilizers can occur.
No generation equality is claimed here. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

noncomputable section

/-- Local presentability supplies a small strong generator and hence well-poweredness. -/
theorem wellPowered : WellPowered.{u} (C ⥤ SSet.{u}) := by
  letI : IsLocallyPresentable.{u} (C ⥤ SSet.{u}) :=
    ProjectiveKanDiagram.locallyPresentable C
  obtain ⟨κ, hκ, hLocal⟩ := IsLocallyPresentable.exists_cardinal (C ⥤ SSet.{u})
  letI := hκ
  letI := hLocal
  obtain ⟨P, hP, hStrong, _⟩ :=
    (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator (C ⥤ SSet.{u}) κ).mp
      inferInstance
  letI := hP
  exact wellPowered_of_isDetecting hStrong.isSeparating.isDetecting

/-- Indices of all subobjects of the free simplex diagrams. -/
def SubrepresentableIndex : Type u := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  exact Σ c : C, Σ n : ℕ,
    Shrink.{u} (Subobject ((ProjectiveKanDiagram.free C c).obj Δ[n]))

/-- The inclusion represented by a chosen subobject of a free simplex diagram. -/
def subrepresentableArrow (i : SubrepresentableIndex C) : Arrow (C ⥤ SSet.{u}) := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  let S : Subobject ((ProjectiveKanDiagram.free C i.1).obj Δ[i.2.1]) :=
    (equivShrink _).symm i.2.2
  exact Arrow.mk S.arrow

/-- Every subrepresentable arrow is a monomorphism. -/
theorem subrepresentableArrow_mono (i : SubrepresentableIndex C) :
    Mono (subrepresentableArrow C i).hom := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  change Mono (((equivShrink _).symm i.2.2 : Subobject
    ((ProjectiveKanDiagram.free C i.1).obj Δ[i.2.1])).arrow)
  infer_instance

/-- A small test family of subrepresentable monomorphisms; not all injective cofibrations. -/
def subrepresentableGenerators : MorphismProperty (C ⥤ SSet.{u}) :=
  ofHoms (fun i : SubrepresentableIndex C ↦ (subrepresentableArrow C i).hom)

instance subrepresentableGenerators_small :
    IsSmall.{u} (subrepresentableGenerators C) :=
  isSmall_ofHoms _

/-- All members of the subrepresentable test family are injective cofibrations. -/
theorem subrepresentableGenerators_le_cofibrations :
    subrepresentableGenerators C ≤ cofibrations C := by
  intro X Y f hf
  obtain ⟨i⟩ := hf
  exact subrepresentableArrow_mono C i

/-- The small subrepresentable family admits the small object argument. -/
theorem subrepresentableGenerators_smallObjectArgument :
    HasSmallObjectArgument.{u} (subrepresentableGenerators C) := by
  letI : IsLocallyPresentable.{u} (C ⥤ SSet.{u}) :=
    ProjectiveKanDiagram.locallyPresentable C
  exact DaggerSmithSolutionSet.smallObjectArgument (subrepresentableGenerators C)

/-- A pointwise trivial Kan fibration, extended to diagrams by the right
adjoint of evaluation, lifts against every subrepresentable generator. -/
theorem subrepresentableGenerators_rlp_evaluationRightAdjoint_trivialFibration
    (c : C) {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : HomotopicalAlgebra.trivialFibrations SSet.{u} p) :
    (subrepresentableGenerators C).rlp
      ((evaluationRightAdjoint SSet.{u} c).map p) := by
  intro A B i hi
  obtain ⟨g⟩ := hi
  have hm : Mono ((subrepresentableArrow C g).hom.app c) :=
    (NatTrans.mono_iff_mono_app _).mp (subrepresentableArrow_mono C g) c
  have hr : (monomorphisms SSet.{u}).rlp p := by
    rw [← SSet.modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp]
    rwa [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  have hl : HasLiftingProperty ((subrepresentableArrow C g).hom.app c) p :=
    hr _ (.infer_property _)
  exact ((evaluationAdjunctionLeft SSet.{u} c).hasLiftingProperty_iff
    (subrepresentableArrow C g).hom p).mp hl

/-- The subrepresentable family yields a canonical weak factorization system. -/
theorem subrepresentableWeakFactorizationSystem :
    IsWeakFactorizationSystem (subrepresentableGenerators C).rlp.llp
      (subrepresentableGenerators C).rlp := by
  letI := subrepresentableGenerators_smallObjectArgument C
  apply IsWeakFactorizationSystem.mk'
  intro A B X Y i p hi hp
  exact hi p hp

/-- Every map in the subrepresentable-generated left class is a levelwise Kan cofibration. -/
theorem generatedCofibrations_levelwiseCofibrations {F G : C ⥤ SSet.{u}}
    (f : F ⟶ G) (hf : (subrepresentableGenerators C).rlp.llp f) :
    (HomotopicalAlgebra.cofibrations SSet.{u}).functorCategory C f := by
  intro c
  rw [← HomotopicalAlgebra.trivialFibrations_llp]
  intro X Y p hp
  have hr : (subrepresentableGenerators C).rlp
      ((evaluationRightAdjoint SSet.{u} c).map p) :=
    subrepresentableGenerators_rlp_evaluationRightAdjoint_trivialFibration C c p hp
  exact ((evaluationAdjunctionLeft SSet.{u} c).hasLiftingProperty_iff f p).mpr
    (hf _ hr)

/-- The subrepresentable-generated left class sits inside the intended injective cofibrations. -/
theorem generatedCofibrations_le_cofibrations :
    (subrepresentableGenerators C).rlp.llp ≤ cofibrations C := by
  intro F G f hf
  change Mono f
  rw [NatTrans.mono_iff_mono_app]
  intro c
  have hc := generatedCofibrations_levelwiseCofibrations C f hf c
  exact (SSet.modelCategoryQuillen.cofibration_iff (f.app c)).mp
    ((HomotopicalAlgebra.cofibration_iff (f.app c)).mpr hc)

/-- The free simplex diagram used as a source of quotient diagrams. -/
def freeSimplexDiagram (c : C) (n : ℕ) : C ⥤ SSet.{u} :=
  (ProjectiveKanDiagram.free C c).obj Δ[n]

/-- A small index for all binary relations on a free simplex diagram. -/
def RelationIndex (c : C) (n : ℕ) : Type u := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  exact Shrink.{u} (Subobject (freeSimplexDiagram C c n ⨯ freeSimplexDiagram C c n))

/-- Recover the represented subobject of the square of a free simplex diagram. -/
def relation (c : C) (n : ℕ) (r : RelationIndex C c n) :
    Subobject (freeSimplexDiagram C c n ⨯ freeSimplexDiagram C c n) := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  exact (equivShrink _).symm r

/-- Coequalize the two projections of an arbitrary small relation. -/
def relationQuotient (c : C) (n : ℕ) (r : RelationIndex C c n) :
    C ⥤ SSet.{u} :=
  coequalizer ((relation C c n r).arrow ≫ prod.fst)
    ((relation C c n r).arrow ≫ prod.snd)

/-- The indices for subobjects of all relation quotients. -/
def QuotientSubobjectIndex : Type u := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  exact Σ c : C, Σ n : ℕ, Σ r : RelationIndex C c n,
    Shrink.{u} (Subobject (relationQuotient C c n r))

/-- The inclusion of a subobject of a relation quotient. -/
def quotientSubobjectArrow (i : QuotientSubobjectIndex C) :
    Arrow (C ⥤ SSet.{u}) := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  let Q := relationQuotient C i.1 i.2.1 i.2.2.1
  let S : Subobject Q := (equivShrink _).symm i.2.2.2
  exact Arrow.mk S.arrow

/-- The quotient-subobject test family, allowing quotients of free simplex diagrams. -/
def quotientSubobjectGenerators : MorphismProperty (C ⥤ SSet.{u}) :=
  ofHoms (fun i : QuotientSubobjectIndex C ↦ (quotientSubobjectArrow C i).hom)

instance quotientSubobjectGenerators_small :
    IsSmall.{u} (quotientSubobjectGenerators C) :=
  isSmall_ofHoms _

/-- Every quotient-subobject inclusion is a monomorphism. -/
theorem quotientSubobjectArrow_mono (i : QuotientSubobjectIndex C) :
    Mono (quotientSubobjectArrow C i).hom := by
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  change Mono (((equivShrink _).symm i.2.2.2 : Subobject
    (relationQuotient C i.1 i.2.1 i.2.2.1)).arrow)
  infer_instance

/-- All members of the quotient-subobject family are injective cofibrations. -/
theorem quotientSubobjectGenerators_le_cofibrations :
    quotientSubobjectGenerators C ≤ cofibrations C := by
  intro X Y f hf
  obtain ⟨i⟩ := hf
  exact quotientSubobjectArrow_mono C i

/-- The quotient-subobject family admits the small object argument. -/
theorem quotientSubobjectGenerators_smallObjectArgument :
    HasSmallObjectArgument.{u} (quotientSubobjectGenerators C) := by
  letI : IsLocallyPresentable.{u} (C ⥤ SSet.{u}) :=
    ProjectiveKanDiagram.locallyPresentable C
  exact DaggerSmithSolutionSet.smallObjectArgument (quotientSubobjectGenerators C)

/-- An unconditional WFS generated by subobjects of relation quotients. -/
theorem quotientSubobjectWeakFactorizationSystem :
    IsWeakFactorizationSystem (quotientSubobjectGenerators C).rlp.llp
      (quotientSubobjectGenerators C).rlp := by
  letI := quotientSubobjectGenerators_smallObjectArgument C
  apply IsWeakFactorizationSystem.mk'
  intro A B X Y i p hi hp
  exact hi p hp

/-- Evaluation's right adjoint sends trivial Kan fibrations to right maps against
any family of diagram monomorphisms. -/
theorem monoFamily_rlp_evaluationRightAdjoint_trivialFibration
    (I : MorphismProperty (C ⥤ SSet.{u})) (hI : I ≤ cofibrations C)
    (c : C) {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : HomotopicalAlgebra.trivialFibrations SSet.{u} p) :
    I.rlp ((evaluationRightAdjoint SSet.{u} c).map p) := by
  intro A B i hi
  have hm : Mono (i.app c) :=
    (NatTrans.mono_iff_mono_app _).mp (show Mono i from hI i hi) c
  have hr : (monomorphisms SSet.{u}).rlp p := by
    rw [← SSet.modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp]
    rwa [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  have hl : HasLiftingProperty (i.app c) p := hr _ (.infer_property _)
  exact ((evaluationAdjunctionLeft SSet.{u} c).hasLiftingProperty_iff i p).mp hl

/-- A left class generated by diagram monomorphisms consists of diagram monomorphisms. -/
theorem monoFamily_generated_le_cofibrations
    (I : MorphismProperty (C ⥤ SSet.{u})) (hI : I ≤ cofibrations C) :
    I.rlp.llp ≤ cofibrations C := by
  intro F G f hf
  change Mono f
  rw [NatTrans.mono_iff_mono_app]
  intro c
  have hc : (HomotopicalAlgebra.trivialFibrations SSet.{u}).llp (f.app c) := by
    intro X Y p hp
    have hr := monoFamily_rlp_evaluationRightAdjoint_trivialFibration C I hI c p hp
    exact ((evaluationAdjunctionLeft SSet.{u} c).hasLiftingProperty_iff f p).mpr
      (hf _ hr)
  have hcof : HomotopicalAlgebra.cofibrations SSet.{u} (f.app c) := by
    rw [← HomotopicalAlgebra.trivialFibrations_llp]
    exact hc
  exact (SSet.modelCategoryQuillen.cofibration_iff (f.app c)).mp
    ((HomotopicalAlgebra.cofibration_iff (f.app c)).mpr hcof)

/-- The quotient-subobject WFS also has only injective cofibrations on its left. -/
theorem quotientGeneratedCofibrations_le_cofibrations :
    (quotientSubobjectGenerators C).rlp.llp ≤ cofibrations C :=
  monoFamily_generated_le_cofibrations C (quotientSubobjectGenerators C)
    (quotientSubobjectGenerators_le_cofibrations C)

end

end DaggerModels.PartII.InjectiveKanDiagram
