import DaggerModelsPartII.DiagramPushoutProduct
import DaggerModelsPartII.InjectiveKanModel
import DaggerModelsPartII.DiagramMappingPrecompFibration
import DaggerModelsPartII.LocalEquivalenceClasses

/-!
# Small boundary boxes for localization of injective diagram models

For a small family of monomorphisms of simplicial-set diagrams, box each map
with every simplicial boundary inclusion and adjoin the chosen injective Smith
trivial-cofibration generators.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

noncomputable section

local instance localizingInjectiveModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- The boundary box of a diagram arrow and a simplicial degree. -/
def localizingBoundaryBox {A B : C ⥤ SSet.{u}} (s : A ⟶ B) (n : ℕ) :=
  (diagramPushoutProduct C s (SSet.boundary n).ι).ι

/-- A small family of all boundary boxes of the chosen diagram arrows. -/
def localizingBoundaryBoxes (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) :
    MorphismProperty (C ⥤ SSet.{u}) :=
  ofHoms (fun p : I × ℕ ↦ localizingBoundaryBox C (s p.1).hom p.2)

/-- The original small family of diagram maps being localized. -/
def diagramLocalizingFamily (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) :
    MorphismProperty (C ⥤ SSet.{u}) :=
  ofHoms (fun i ↦ (s i).hom)

instance diagramLocalizingFamily_small (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) :
    IsSmall.{u} (diagramLocalizingFamily C I s) := isSmall_ofHoms _

instance localizingBoundaryBoxes_small (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) :
    IsSmall.{u} (localizingBoundaryBoxes C I s) := isSmall_ofHoms _

/-- Boundary boxes of monomorphisms are injective cofibrations. -/
theorem localizingBoundaryBoxes_le_cofibrations (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom) :
    localizingBoundaryBoxes C I s ≤
      HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) := by
  intro A B f hf
  obtain ⟨⟨i, n⟩⟩ := hf
  letI : Mono (s i).hom := hs i
  have hm : Mono (localizingBoundaryBox C (s i).hom n) :=
    diagramPushoutProduct_mono C (s i).hom (SSet.boundary n).ι
      (diagramPushoutProduct C (s i).hom (SSet.boundary n).ι)
  rw [model_cofibrations C]
  exact hm

/-- The explicit small Smith generators for injective trivial cofibrations. -/
def injectiveSmithJ : MorphismProperty (C ⥤ SSet.{u}) :=
  letI := ProjectiveKanDiagram.locallyPresentable C
  DaggerSmithSolutionSet.J (injectiveSolutionSet C)

instance injectiveSmithJ_small : IsSmall.{u} (injectiveSmithJ C) :=
  (combinatorialData C).smallJ

/-- Every chosen injective Smith generator is a trivial cofibration. -/
theorem injectiveSmithJ_le_trivialCofibrations :
    injectiveSmithJ C ≤ HomotopicalAlgebra.trivialCofibrations (C ⥤ SSet.{u}) := by
  let d := combinatorialData C
  intro A B f hf
  have hj : (injectiveSmithJ C).rlp.llp f := (le_llp_rlp _) f hf
  change d.model.categoryWithCofibrations.cofibrations f ∧
    d.model.categoryWithWeakEquivalences.weakEquivalences f
  rw [d.modelCof, d.modelWeak]
  change ((quotientSubobjectGenerators C).rlp.llp ⊓ weakEquivalences C) f
  rw [← d.trivialCofibrations]
  exact hj

/-- Right lifting against the Smith generators is injective fibration. -/
theorem injectiveSmithJ_rlp_eq_fibrations :
    (injectiveSmithJ C).rlp = HomotopicalAlgebra.fibrations (C ⥤ SSet.{u}) := by
  let d := combinatorialData C
  change (injectiveSmithJ C).rlp = d.model.categoryWithFibrations.fibrations
  exact d.fibrations

/-- The joint small family for injective and local fibrancy. -/
def localizingFibrancyGenerators (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) :
    MorphismProperty (C ⥤ SSet.{u}) :=
  injectiveSmithJ C ⊔ localizingBoundaryBoxes C I s

instance localizingFibrancyGenerators_small (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) :
    IsSmall.{u} (localizingFibrancyGenerators C I s) := by
  constructor
  change Small.{u} ((injectiveSmithJ C).toSet ∪
    (localizingBoundaryBoxes C I s).toSet : Set (Arrow (C ⥤ SSet.{u})))
  infer_instance

/-- The joint family consists of injective cofibrations when each localizer is mono. -/
theorem localizingFibrancyGenerators_le_cofibrations (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom) :
    localizingFibrancyGenerators C I s ≤
      HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) := by
  refine sup_le ?_ (localizingBoundaryBoxes_le_cofibrations C I s hs)
  intro A B f hf
  exact (injectiveSmithJ_le_trivialCofibrations C f hf).1

/-- The joint small family admits the small object argument. -/
theorem localizingFibrancyGenerators_smallObjectArgument (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) :
    HasSmallObjectArgument.{u} (localizingFibrancyGenerators C I s) := by
  letI := ProjectiveKanDiagram.locallyPresentable C
  letI := localizingFibrancyGenerators_small C I s
  exact DaggerSmithSolutionSet.smallObjectArgument _

/-- Right lifting against all boundary boxes is componentwise right lifting. -/
theorem localizingBoundaryBoxes_rlp_terminal_iff (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (W : C ⥤ SSet.{u}) :
    (localizingBoundaryBoxes C I s).rlp (terminal.from W) ↔
      ∀ i n, HasLiftingProperty (localizingBoundaryBox C (s i).hom n) (terminal.from W) := by
  constructor
  · intro h i n
    exact h _ ⟨(i, n)⟩
  · intro h A B f hf
    obtain ⟨⟨i, n⟩⟩ := hf
    exact h i n

/-- Right lifting against the joint family is injective fibrancy plus all local boxes. -/
theorem localizingFibrancyGenerators_rlp_terminal_iff (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (W : C ⥤ SSet.{u}) :
    (localizingFibrancyGenerators C I s).rlp (terminal.from W) ↔
      IsFibrant W ∧
        ∀ i n, HasLiftingProperty (localizingBoundaryBox C (s i).hom n)
          (terminal.from W) := by
  constructor
  · intro h
    have hj : (injectiveSmithJ C).rlp (terminal.from W) := by
      intro A B f hf
      exact h f (Or.inl hf)
    have hW : IsFibrant W := by
      apply (isFibrant_iff_of_isTerminal (terminal.from W) terminalIsTerminal).mpr
      apply (fibration_iff _).mpr
      rw [← injectiveSmithJ_rlp_eq_fibrations C]
      exact hj
    refine ⟨hW, ?_⟩
    exact (localizingBoundaryBoxes_rlp_terminal_iff C I s W).mp (by
      intro A B f hf
      exact h f (Or.inr hf))
  · rintro ⟨hW, hb⟩ A B f hf
    rcases hf with hf | hf
    · have hj : (injectiveSmithJ C).rlp (terminal.from W) := by
        rw [injectiveSmithJ_rlp_eq_fibrations C]
        letI := hW
        exact mem_fibrations _
      exact hj f hf
    · exact (localizingBoundaryBoxes_rlp_terminal_iff C I s W).mpr hb f hf

/-- Terminal lifting against the joint family is injective fibrancy together
with the strict weak-equivalence test for every chosen localizing map. -/
theorem localizingFibrancyGenerators_rlp_terminal_iff_strict (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom)
    (W : C ⥤ SSet.{u}) :
    (localizingFibrancyGenerators C I s).rlp (terminal.from W) ↔
      IsFibrant W ∧ ∀ i,
        HomotopicalAlgebra.weakEquivalences SSet.{u}
          (diagramMappingPrecomp (s i).hom W) := by
  rw [localizingFibrancyGenerators_rlp_terminal_iff C I s W]
  constructor
  · rintro ⟨hW, hboxes⟩
    refine ⟨hW, fun i ↦ ?_⟩
    have hboundary : ∀ n : ℕ,
        HasLiftingProperty (SSet.boundary.{u} n).ι
          (diagramMappingPrecomp (s i).hom W) := by
      intro n
      exact (diagramPushoutProduct_hasLiftingProperty_terminal_iff C (s i).hom
        (SSet.boundary n).ι W
        (diagramPushoutProduct C (s i).hom (SSet.boundary n).ι)).mp (hboxes i n)
    exact (weakEquivalence_iff _).mp
      ((DaggerModels.KanQuillenReuse.boundary_lifting_iff_trivial _).mp hboundary).2
  · rintro ⟨hW, hstrict⟩
    refine ⟨hW, fun i n ↦ ?_⟩
    letI : Mono (s i).hom := hs i
    letI : IsFibrant W := hW
    have hfib : Fibration (diagramMappingPrecomp (s i).hom W) :=
      diagramMappingPrecomp_isFibration C (s i).hom W
    have hweak : WeakEquivalence (diagramMappingPrecomp (s i).hom W) :=
      (weakEquivalence_iff _).mpr (hstrict i)
    have hboundary : HasLiftingProperty (SSet.boundary.{u} n).ι
        (diagramMappingPrecomp (s i).hom W) :=
      (DaggerModels.KanQuillenReuse.boundary_lifting_iff_trivial _).mpr
        ⟨hfib, hweak⟩ n
    exact (diagramPushoutProduct_hasLiftingProperty_terminal_iff C (s i).hom
      (SSet.boundary n).ι W
      (diagramPushoutProduct C (s i).hom (SSet.boundary n).ι)).mpr hboundary

/-- The joint terminal lifting test is exactly local-object fibrancy for the
original small family in the injective model. -/
theorem localizingFibrancyGenerators_rlp_terminal_iff_localObject (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom)
    (W : C ⥤ SSet.{u}) :
    (localizingFibrancyGenerators C I s).rlp (terminal.from W) ↔
      Localization.localObject (diagramLocalizingFamily C I s) W := by
  rw [localizingFibrancyGenerators_rlp_terminal_iff_strict C I s hs W]
  constructor
  · rintro ⟨hW, hstrict⟩
    letI : IsFibrant W := hW
    refine ⟨hW, ?_⟩
    intro A B f hf
    obtain ⟨i⟩ := hf
    exact (model_homotopyMapping_iff_strict C (s i).hom).mpr (hstrict i)
  · rintro ⟨hW, hlocal⟩
    letI : IsFibrant W := hW
    refine ⟨hW, fun i ↦ ?_⟩
    exact (model_homotopyMapping_iff_strict C (s i).hom).mp (hlocal _ ⟨i⟩)

end

end DaggerModels.PartII.InjectiveKanDiagram
