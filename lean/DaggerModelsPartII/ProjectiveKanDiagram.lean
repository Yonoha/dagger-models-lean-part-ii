import TopCatModelCategory.ModelCategorySSet
import NativeSSetLocallyPresentable
import OriginalAdjunctionMappedLifting
import OriginalSmithCardinalRecovered
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Limits
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.CategoryTheory.Presentable.Presheaf

/-!
# Projective Kan generators on simplicial-set diagrams

The free diagram at `c` is the left adjoint to evaluation at `c`.  Applying it
to the ordinary boundary and horn inclusions gives the projective generators.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Opposite
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

noncomputable section

/-- The free simplicial-set diagram at an index object. -/
def free (c : C) : SSet.{u} ⥤ C ⥤ SSet.{u} :=
  evaluationLeftAdjoint SSet.{u} c

/-- Levelwise weak homotopy equivalences. -/
def weakEquivalences : MorphismProperty (C ⥤ SSet.{u}) :=
  (HomotopicalAlgebra.weakEquivalences SSet.{u}).functorCategory C

/-- Levelwise Kan fibrations. -/
def fibrations : MorphismProperty (C ⥤ SSet.{u}) :=
  (HomotopicalAlgebra.fibrations SSet.{u}).functorCategory C

/-- The projective trivial fibrations are precisely levelwise trivial Kan fibrations. -/
theorem fibrations_inf_weakEquivalences :
    fibrations C ⊓ weakEquivalences C =
      (trivialFibrations SSet.{u}).functorCategory C := by
  ext X Y f
  constructor
  · rintro ⟨hf, hw⟩ c
    exact (mem_trivialFibrations_iff (f.app c)).mpr
      ⟨(fibration_iff _).mpr (hf c), (weakEquivalence_iff _).mpr (hw c)⟩
  · intro h
    exact ⟨fun c ↦ (fibration_iff _).mp
      ((mem_trivialFibrations_iff (f.app c)).mp (h c)).1,
      fun c ↦ (weakEquivalence_iff _).mp
        ((mem_trivialFibrations_iff (f.app c)).mp (h c)).2⟩

instance weakEquivalences_hasTwoOutOfThree :
    (weakEquivalences C).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := fun c ↦ (HomotopicalAlgebra.weakEquivalences SSet.{u}).comp_mem
    (f.app c) (g.app c) (hf c) (hg c)
  of_precomp f g hf hfg := fun c ↦
    (HomotopicalAlgebra.weakEquivalences SSet.{u}).of_precomp
      (f.app c) (g.app c) (hf c) (hfg c)
  of_postcomp f g hg hfg := fun c ↦
    (HomotopicalAlgebra.weakEquivalences SSet.{u}).of_postcomp
      (f.app c) (g.app c) (hg c) (hfg c)

/-- Free boundary inclusions, indexed by objects of `C` and simplex degrees. -/
def boundaryGenerators : MorphismProperty (C ⥤ SSet.{u}) :=
  ofHoms (fun g : C × ℕ ↦ (free C g.1).map (SSet.boundary g.2).ι)

/-- Free horn inclusions, indexed by objects of `C` and positive simplex degrees. -/
def hornGenerators : MorphismProperty (C ⥤ SSet.{u}) :=
  ofHoms (fun g : C × (Σ n : ℕ, Fin (n + 2)) ↦
    (free C g.1).map (SSet.horn (g.2.1 + 1) g.2.2).ι)

instance boundaryGenerators_small : IsSmall.{u} (boundaryGenerators C) :=
  isSmall_ofHoms _

instance hornGenerators_small : IsSmall.{u} (hornGenerators C) :=
  isSmall_ofHoms _

/-- The underlying diagram category is locally presentable. -/
theorem locallyPresentable : IsLocallyPresentable.{u} (C ⥤ SSet.{u}) := by
  let e : (Cᵒᵖᵒᵖ ⥤ SSet.{u}) ≌ (C ⥤ SSet.{u}) :=
    (opOpEquivalence C).congrLeft
  letI : IsLocallyPresentable.{u} SSet.{u} :=
    DaggerNativeSSetLocallyPresentable.locallyPresentable
  have : IsLocallyPresentable.{u} (Cᵒᵖᵒᵖ ⥤ SSet.{u}) := inferInstance
  exact e.isLocallyPresentable

/-- Small object arguments for both explicit projective generator families. -/
theorem boundaryGenerators_smallObjectArgument :
    HasSmallObjectArgument.{u} (boundaryGenerators C) := by
  letI := locallyPresentable C
  exact DaggerSmithSolutionSet.smallObjectArgument (boundaryGenerators C)

theorem hornGenerators_smallObjectArgument :
    HasSmallObjectArgument.{u} (hornGenerators C) := by
  letI := locallyPresentable C
  exact DaggerSmithSolutionSet.smallObjectArgument (hornGenerators C)

/-- Lifting against free boundaries is exactly levelwise trivial fibrancy. -/
theorem boundaryGenerators_rlp :
    (boundaryGenerators C).rlp =
      (trivialFibrations SSet.{u}).functorCategory C := by
  ext X Y p
  constructor
  · intro hp c
    rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
    intro A B i hi
    obtain ⟨n⟩ := hi
    exact ((evaluationAdjunctionRight SSet.{u} c).hasLiftingProperty_iff
      (SSet.boundary n).ι p).mp (hp _ ⟨(c, n)⟩)
  · intro hp A B i hi
    obtain ⟨⟨c, n⟩⟩ := hi
    apply ((evaluationAdjunctionRight SSet.{u} c).hasLiftingProperty_iff
      (SSet.boundary n).ι p).mpr
    rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations] at hp
    exact hp c _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n)

/-- Lifting against free horns is exactly levelwise Kan fibrancy. -/
theorem hornGenerators_rlp :
    (hornGenerators C).rlp = fibrations C := by
  ext X Y p
  constructor
  · intro hp c
    rw [SSet.modelCategoryQuillen.fibrations_eq]
    intro A B i hi
    simp only [SSet.modelCategoryQuillen.J, iSup_iff] at hi
    obtain ⟨n, ⟨k⟩⟩ := hi
    have hg : hornGenerators C ((free C c).map (SSet.horn (n + 1) k).ι) :=
      by
        unfold hornGenerators free
        exact .mk (c, (Sigma.mk n k : Σ m : ℕ, Fin (m + 2)))
    exact ((evaluationAdjunctionRight SSet.{u} c).hasLiftingProperty_iff
      (SSet.horn (n + 1) k).ι p).mp (hp _ hg)
  · intro hp A B i hi
    obtain ⟨⟨c, ⟨n, k⟩⟩⟩ := hi
    apply ((evaluationAdjunctionRight SSet.{u} c).hasLiftingProperty_iff
      (SSet.horn (n + 1) k).ι p).mpr
    have hpc : HomotopicalAlgebra.fibrations SSet.{u} (p.app c) := hp c
    rw [SSet.modelCategoryQuillen.fibrations_eq] at hpc
    exact hpc _ (SSet.modelCategoryQuillen.horn_ι_mem_J n k)

/-- The boundary small object argument gives an exact projective WFS. -/
theorem boundaryWeakFactorizationSystem :
    IsWeakFactorizationSystem (boundaryGenerators C).rlp.llp
      ((trivialFibrations SSet.{u}).functorCategory C) := by
  rw [← boundaryGenerators_rlp C]
  letI := boundaryGenerators_smallObjectArgument C
  apply IsWeakFactorizationSystem.mk'
  intro A B X Y i p hi hp
  exact hi p hp

/-- The horn small object argument gives the other exact projective WFS. -/
theorem hornWeakFactorizationSystem :
    IsWeakFactorizationSystem (hornGenerators C).rlp.llp (fibrations C) := by
  rw [← hornGenerators_rlp C]
  letI := hornGenerators_smallObjectArgument C
  apply IsWeakFactorizationSystem.mk'
  intro A B X Y i p hi hp
  exact hi p hp

/-- The horn-generated left class is contained in the boundary-generated left class. -/
theorem hornCofibrations_le_boundaryCofibrations :
    (hornGenerators C).rlp.llp ≤ (boundaryGenerators C).rlp.llp := by
  apply antitone_llp
  rw [boundaryGenerators_rlp C, hornGenerators_rlp C]
  intro X Y p hp c
  exact (fibration_iff _).mp ((mem_trivialFibrations_iff (p.app c)).mp (hp c)).1

/-- The right adjoint of evaluation sends a Kan fibration to a levelwise Kan fibration. -/
theorem evaluationRightAdjoint_fibration (c : C) {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : HomotopicalAlgebra.fibrations SSet.{u} p) :
    fibrations C ((evaluationRightAdjoint SSet.{u} c).map p) := by
  intro d
  change HomotopicalAlgebra.fibrations SSet.{u}
    (Limits.Pi.map (f := fun _ : d ⟶ c ↦ X) (g := fun _ : d ⟶ c ↦ Y)
      (fun _ ↦ p))
  rw [SSet.modelCategoryQuillen.fibrations_eq]
  intro A B i hi
  have h : ∀ _ : d ⟶ c, HasLiftingProperty i p := fun _ ↦ hp i hi
  infer_instance

/-- The right adjoint of evaluation also preserves trivial Kan fibrations. -/
theorem evaluationRightAdjoint_trivialFibration (c : C) {X Y : SSet.{u}}
    (p : X ⟶ Y) (hp : trivialFibrations SSet.{u} p) :
    (trivialFibrations SSet.{u}).functorCategory C
      ((evaluationRightAdjoint SSet.{u} c).map p) := by
  intro d
  change trivialFibrations SSet.{u}
    (Limits.Pi.map (f := fun _ : d ⟶ c ↦ X) (g := fun _ : d ⟶ c ↦ Y)
      (fun _ ↦ p))
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  intro A B i hi
  have hprlp : SSet.modelCategoryQuillen.I.{u}.rlp p := by
    rw [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
    exact hp
  have h : ∀ _ : d ⟶ c, HasLiftingProperty i p := fun _ ↦ hprlp i hi
  infer_instance

/-- Boundary-generated projective cofibrations are levelwise Kan cofibrations. -/
theorem boundaryCofibrations_levelwiseCofibrations {F G : C ⥤ SSet.{u}}
    (f : F ⟶ G) (hf : (boundaryGenerators C).rlp.llp f) :
    (cofibrations SSet.{u}).functorCategory C f := by
  intro c
  rw [← trivialFibrations_llp]
  intro X Y p hp
  have hr : (boundaryGenerators C).rlp
      ((evaluationRightAdjoint SSet.{u} c).map p) := by
    rw [boundaryGenerators_rlp C]
    exact evaluationRightAdjoint_trivialFibration C c p hp
  exact ((evaluationAdjunctionLeft SSet.{u} c).hasLiftingProperty_iff f p).mpr
    (hf _ hr)

/-- Every projective cofibration is a monomorphism at each diagram object. -/
theorem boundaryCofibrations_levelwiseMono {F G : C ⥤ SSet.{u}}
    (f : F ⟶ G) (hf : (boundaryGenerators C).rlp.llp f) (c : C) :
    Mono (f.app c) := by
  have h := boundaryCofibrations_levelwiseCofibrations C f hf c
  exact (SSet.modelCategoryQuillen.cofibration_iff (f.app c)).mp
    ((cofibration_iff (f.app c)).mpr h)

/-- Every horn-generated left map is a levelwise trivial Kan cofibration. -/
theorem hornCofibrations_levelwiseTrivialCofibrations {F G : C ⥤ SSet.{u}}
    (f : F ⟶ G) (hf : (hornGenerators C).rlp.llp f) :
    (trivialCofibrations SSet.{u}).functorCategory C f := by
  intro c
  rw [← fibrations_llp]
  intro X Y p hp
  have hr : (hornGenerators C).rlp
      ((evaluationRightAdjoint SSet.{u} c).map p) := by
    rw [hornGenerators_rlp C]
    exact evaluationRightAdjoint_fibration C c p hp
  exact ((evaluationAdjunctionLeft SSet.{u} c).hasLiftingProperty_iff f p).mpr
    (hf _ hr)

/-- In particular, horn-generated left maps are levelwise weak equivalences. -/
theorem hornCofibrations_levelwiseWeakEquivalences :
    (hornGenerators C).rlp.llp ≤ weakEquivalences C := by
  intro F G f hf c
  have h := hornCofibrations_levelwiseTrivialCofibrations C f hf c
  exact (weakEquivalence_iff _).mp ((mem_trivialCofibrations_iff (f.app c)).mp h).2

/-- The weak boundary-generated cofibrations are exactly horn-generated cofibrations. -/
theorem boundaryCofibrations_inf_weakEquivalences :
    (boundaryGenerators C).rlp.llp ⊓ weakEquivalences C =
      (hornGenerators C).rlp.llp := by
  apply le_antisymm
  · intro F G f hf
    letI : HasFactorization (hornGenerators C).rlp.llp (fibrations C) :=
      (hornWeakFactorizationSystem C).hasFactorization
    let q := factorizationData (hornGenerators C).rlp.llp (fibrations C) f
    have hqi : weakEquivalences C q.i :=
      hornCofibrations_levelwiseWeakEquivalences C q.i q.hi
    have hqpW : weakEquivalences C q.p :=
      (weakEquivalences C).of_precomp q.i q.p hqi (by rw [q.fac]; exact hf.2)
    have hqpF : fibrations C q.p := q.hp
    have hqpI : (boundaryGenerators C).rlp q.p := by
      rw [boundaryGenerators_rlp C]
      rw [← fibrations_inf_weakEquivalences C]
      exact ⟨hqpF, hqpW⟩
    have hlift : HasLiftingProperty f q.p := hf.1 q.p hqpI
    exact (hornGenerators C).rlp.llp.of_retract
      (RetractArrow.ofLeftLiftingProperty q.fac) q.hi
  · intro F G f hf
    exact ⟨hornCofibrations_le_boundaryCofibrations C f hf,
      hornCofibrations_levelwiseWeakEquivalences C f hf⟩

/-- The projective Kan model structure on diagrams indexed by any small category. -/
noncomputable def modelCategory : ModelCategory (C ⥤ SSet.{u}) := by
  let D := C ⥤ SSet.{u}
  letI : CategoryWithCofibrations D := ⟨(boundaryGenerators C).rlp.llp⟩
  letI : CategoryWithFibrations D := ⟨fibrations C⟩
  letI : CategoryWithWeakEquivalences D := ⟨weakEquivalences C⟩
  letI : (HomotopicalAlgebra.weakEquivalences D).HasTwoOutOfThreeProperty :=
    weakEquivalences_hasTwoOutOfThree C
  letI : IsWeakFactorizationSystem (cofibrations D) (trivialFibrations D) := by
    change IsWeakFactorizationSystem (boundaryGenerators C).rlp.llp
      (fibrations C ⊓ weakEquivalences C)
    rw [fibrations_inf_weakEquivalences C]
    exact boundaryWeakFactorizationSystem C
  letI : IsWeakFactorizationSystem (trivialCofibrations D) (HomotopicalAlgebra.fibrations D) := by
    change IsWeakFactorizationSystem
      ((boundaryGenerators C).rlp.llp ⊓ weakEquivalences C) (fibrations C)
    rw [boundaryCofibrations_inf_weakEquivalences C]
    exact hornWeakFactorizationSystem C
  exact ModelCategory.mk' _

/-- The model structure has the prescribed levelwise Kan fibrations. -/
theorem model_fibrations :
    @HomotopicalAlgebra.fibrations (C ⥤ SSet.{u}) _
      (modelCategory C).categoryWithFibrations = fibrations C := rfl

/-- The model structure has the prescribed levelwise weak homotopy equivalences. -/
theorem model_weakEquivalences :
    @HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) _
      (modelCategory C).categoryWithWeakEquivalences = weakEquivalences C := rfl

/-- The model structure has boundary-generated cofibrations. -/
theorem model_cofibrations :
    @HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) _
      (modelCategory C).categoryWithCofibrations = (boundaryGenerators C).rlp.llp := rfl

/-- Fibrant diagrams in the projective model are exactly the levelwise fibrant diagrams. -/
theorem model_isFibrant_iff (X : C ⥤ SSet.{u}) :
    (letI := modelCategory C; IsFibrant X) ↔ ∀ c, IsFibrant (X.obj c) := by
  letI := modelCategory C
  change IsFibrant X ↔ ∀ c, IsFibrant (X.obj c)
  rw [isFibrant_iff, fibration_iff]
  change (∀ c, HomotopicalAlgebra.fibrations SSet.{u} ((terminal.from X).app c)) ↔ _
  apply forall_congr'
  intro c
  rw [← fibration_iff]
  exact (isFibrant_iff_of_isTerminal _
    (terminalIsTerminal.isTerminalObj ((evaluation C SSet.{u}).obj c))).symm

/-- Explicit small generating families for the projective Kan model structure. -/
theorem combinatorial :
    IsLocallyPresentable.{u} (C ⥤ SSet.{u}) ∧
      ∃ I J : MorphismProperty (C ⥤ SSet.{u}),
        IsSmall.{u} I ∧ IsSmall.{u} J ∧
          HasSmallObjectArgument.{u} I ∧ HasSmallObjectArgument.{u} J ∧
          I.rlp = (trivialFibrations SSet.{u}).functorCategory C ∧
          J.rlp = fibrations C := by
  refine ⟨locallyPresentable C, boundaryGenerators C, hornGenerators C,
    inferInstance, inferInstance, boundaryGenerators_smallObjectArgument C,
    hornGenerators_smallObjectArgument C, ?_, ?_⟩
  · rw [boundaryGenerators_rlp C]
  · rw [hornGenerators_rlp C]

end

end DaggerModels.PartII.ProjectiveKanDiagram
