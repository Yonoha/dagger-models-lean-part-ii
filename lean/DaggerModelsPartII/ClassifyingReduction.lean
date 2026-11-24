import DaggerModelsPartII.LengthFiltrationColimit
import DaggerModelsPartII.NativeUnitMonomorphism
import DaggerModelsPartII.OuterFaceLocalEquivalence
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Conditional reduction of the representable unit to successor stages

This file assumes only that each actual successor length-stage inclusion is a
trivial cofibration. It then transfers the transfinite composite across the
literal spine and representable comparisons to the original adjunction unit.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen
open DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.ClassifyingReduction

open SegalLocalizers SegalRepresentables ActualIndexProjectiveModel
open ActualUnitNativeComparison DaggerNerveLengthOne DaggerNerveLengthFiltration
open NativeUnitMonomorphism LengthFiltrationColimit C2InvolutionActions
open DaggerSimplexNerveNaturality

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

/-- Closure of localized injective trivial cofibrations under the actual
countable transfinite composition. -/
private instance localized_trivialCofibrations_nat_stable :
    (trivialCofibrations ReverseDaggerSpace.{0}).IsStableUnderTransfiniteCompositionOfShape ℕ := by
  rw [← fibrations_llp]
  infer_instance

/-- The conditional successor-stage premise implies that the actual map
from `X₁` into the discrete native nerve is a trivial cofibration. -/
theorem lengthOne_inclusion_trivial_of_successors (m : ℕ)
    (hsucc : ∀ n : ℕ,
      injectiveSegalModel.categoryWithCofibrations.cofibrations
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n))) ∧
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n)))) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        (discreteDiagram.map (lengthFiltration m 1).ι) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (discreteDiagram.map (lengthFiltration m 1).ι) := by
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  let c : (trivialCofibrations ReverseDaggerSpace.{0}).TransfiniteCompositionOfShape ℕ
      (discreteDiagram.map (lengthFiltration m 1).ι) :=
    { toTransfiniteCompositionOfShape := discreteLengthTransfiniteComposition m
      map_mem := fun n hn => hsucc n }
  exact (trivialCofibrations ReverseDaggerSpace.{0}).transfiniteCompositionsOfShape_le
    ℕ _ ⟨c⟩

private theorem spine_eq_top_of_le_one (n : ℕ) (hn : n ≤ 1) :
    DaggerNativeStandardSpineInner.spine.{0} n = ⊤ := by
  apply top_unique
  intro q c hc
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      rw [DaggerNativeStandardSpineInner.mem_spine_iff]
      have hr := (SSet.stdSimplex.asOrderHom c (Fin.last d)).isLt
      omega

/-- Every literal spine map is a weak equivalence in the localized injective
model, including dimensions zero and one where the spine is the simplex. -/
theorem segalMap_localWeak (n : ℕ) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (segalMap n) := by
  by_cases hn : 2 ≤ n
  · letI : ModelCategory ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    have h : InjectiveKanDiagram.diagramLocalizingFamily ReverseSimplexᵒᵖ
        LocalizerIndex localizerArrow (localizerArrow (.inl ⟨n, hn⟩)).hom := by
      exact MorphismProperty.ofHoms.mk (.inl ⟨n, hn⟩ : LocalizerIndex)
    have hw := Localization.family_le_localEquivalences
      (InjectiveKanDiagram.diagramLocalizingFamily ReverseSimplexᵒᵖ
        LocalizerIndex localizerArrow) _ h
    rw [show injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences
        (InjectiveKanDiagram.diagramLocalizingFamily ReverseSimplexᵒᵖ
          LocalizerIndex localizerArrow) from
      (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
        LocalizerIndex localizerArrow localizerArrow_mono).2]
    exact hw
  · have hsmall : n ≤ 1 := by omega
    haveI : IsIso (DaggerNativeStandardSpineInner.spine.{0} n).ι := by
      rw [spine_eq_top_of_le_one n hsmall]
      change IsIso (SSet.Subcomplex.topIso (Δ[n] : SSet.{0})).hom
      infer_instance
    haveI : IsIso (segalMap n) := by
      change IsIso (discreteDagger.map
        (freeDagger.map (DaggerNativeStandardSpineInner.spine.{0} n).ι))
      infer_instance
    exact (weakEquivalences ReverseDaggerSpace.{0}).of_isIso _

/-- The literal free dagger spine map becomes a local weak equivalence
once all successor length-stage inclusions are trivial cofibrations. -/
theorem canonicalSpineMap_localWeak_of_successors (m : ℕ)
    (hsucc : ∀ n : ℕ,
      injectiveSegalModel.categoryWithCofibrations.cofibrations
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n))) ∧
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n)))) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (discreteDagger.map (canonicalSpineMap m)) := by
  let W := weakEquivalences ReverseDaggerSpace.{0}
  have hstage := (lengthOne_inclusion_trivial_of_successors m hsucc).2
  haveI : IsIso (discreteDiagram.map (spineLengthOneIso m).hom) :=
    Functor.map_isIso _ _
  have hiso : W (discreteDiagram.map (spineLengthOneIso m).hom) :=
    W.of_isIso _
  have hcomp := W.comp_mem _ _ hiso hstage
  have heq : discreteDiagram.map (spineLengthOneIso m).hom ≫
        discreteDiagram.map (lengthFiltration m 1).ι =
      discreteDagger.map (canonicalSpineMap m) := by
    calc
      discreteDiagram.map (spineLengthOneIso m).hom ≫
          discreteDiagram.map (lengthFiltration m 1).ι =
          discreteDiagram.map
            ((spineLengthOneIso m).hom ≫ (lengthFiltration m 1).ι) :=
        (discreteDiagram.map_comp _ _).symm
      _ = discreteDiagram.map (canonicalSpinePresheafMap m) := by
        rw [spineLengthOneIso_ι]
      _ = discreteDagger.map (canonicalSpineMap m) := rfl
  exact heq ▸ hcomp

/-- Two-out-of-three across the Segal spine map makes the canonical
free-simplex-to-nerve map locally weak. -/
theorem canonicalDaggerMap_localWeak_of_successors (m : ℕ)
    (hsucc : ∀ n : ℕ,
      injectiveSegalModel.categoryWithCofibrations.cofibrations
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n))) ∧
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n)))) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (discreteDagger.map (canonicalDaggerMap m)) := by
  have hspine := canonicalSpineMap_localWeak_of_successors m hsucc
  have hsegal := segalMap_localWeak m
  have hfac : segalMap m ≫ discreteDagger.map (canonicalDaggerMap m) =
      discreteDagger.map (canonicalSpineMap m) := by
    rw [canonicalSpineMap, discreteDagger.map_comp]
    rfl
  exact injectiveSegalModel.cm2.of_precomp
    (segalMap m) (discreteDagger.map (canonicalDaggerMap m))
    hsegal (hfac ▸ hspine)

/-- The original actual left-extension unit at a reversal representable. -/
def actualRepresentableUnit (m : ℕ) :
    (simplicialYoneda.{0, 0} ReverseSimplex).obj (ReverseSimplex.mk m) ⟶
      (actualRestriction.{0}).obj
        ((actualLeftExtension.{0}).obj
          ((simplicialYoneda.{0, 0} ReverseSimplex).obj
            (ReverseSimplex.mk m))) :=
  (actualLeftAdjunction.{0}).unit.app
    ((simplicialYoneda.{0, 0} ReverseSimplex).obj (ReverseSimplex.mk m))

/-- The chosen target comparison, combining the left-Kan representable
comparison and the native free-path-nerve equivalence. -/
def actualRepresentableTargetIso (m : ℕ) :
    (actualRestriction.{0}).obj
      ((actualLeftExtension.{0}).obj
        ((simplicialYoneda.{0, 0} ReverseSimplex).obj
          (ReverseSimplex.mk m))) ≅
      discreteDagger.obj
        (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)) :=
  (actualRestriction.{0}).mapIso
    ((actualLeftExtension_simplicialYoneda.{0}).app
      (ReverseSimplex.mk m)) ≪≫
    (actualRepresentableNativeDaggerSpaceIso m)

/-- The precise natural square identifying the original actual unit with
the canonical native free-simplex map. -/
theorem actualRepresentableUnit_native_square (m : ℕ) :
    (freeSimplexRepresentable.{0} m).hom ≫
      actualRepresentableUnit m ≫
      (actualRepresentableTargetIso m).hom =
        discreteDagger.map (canonicalDaggerMap m) := by
  change actualUnitNativeMap m =
    discreteDagger.map (canonicalDaggerMap m)
  exact actualUnitNativeMap_eq_canonicalDaggerMap m

/-- The original representable unit is locally weak under the exact
successor-stage trivial-cofibration hypothesis. -/
theorem actualRepresentableUnit_localWeak_of_successors (m : ℕ)
    (hsucc : ∀ n : ℕ,
      injectiveSegalModel.categoryWithCofibrations.cofibrations
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n))) ∧
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n)))) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (actualRepresentableUnit m) := by
  let W := weakEquivalences ReverseDaggerSpace.{0}
  have hcanonical := canonicalDaggerMap_localWeak_of_successors m hsucc
  have hcomm : discreteDagger.map (canonicalDaggerMap m) ≫
      (actualRepresentableTargetIso m).inv =
      (freeSimplexRepresentable.{0} m).hom ≫ actualRepresentableUnit m := by
    have h := actualRepresentableUnit_native_square m
    calc
      discreteDagger.map (canonicalDaggerMap m) ≫
          (actualRepresentableTargetIso m).inv =
          ((freeSimplexRepresentable.{0} m).hom ≫
            actualRepresentableUnit m ≫
            (actualRepresentableTargetIso m).hom) ≫
              (actualRepresentableTargetIso m).inv := by rw [h]
      _ = (freeSimplexRepresentable.{0} m).hom ≫
          actualRepresentableUnit m := by simp [Category.assoc]
  let e : Arrow.mk (discreteDagger.map (canonicalDaggerMap m)) ≅
      Arrow.mk (actualRepresentableUnit m) :=
    Arrow.isoMk (freeSimplexRepresentable.{0} m)
      (actualRepresentableTargetIso m).symm hcomm.symm
  exact (W.arrow_mk_iso_iff e).mp hcanonical

/-- The actual representable unit is an injective-model cofibration, by its
pointwise monomorphism and the unchanged cofibration class of localization. -/
theorem actualRepresentableUnit_cofibration (m : ℕ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
      (actualRepresentableUnit m) := by
  haveI : Mono (actualRepresentableUnit m) :=
    actualUnit_representable_mono.{0} (ReverseSimplex.mk m)
  have h := (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono).1
  rw [h]
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  change cofibrations ReverseDaggerSpace.{0} (actualRepresentableUnit m)
  rw [InjectiveKanDiagram.model_cofibrations]
  exact inferInstanceAs (Mono (actualRepresentableUnit m))

/-- Conditional reduction of the original representable change-of-index unit
to the successor maps of the literal native length filtration. -/
theorem actualRepresentableUnit_trivial_of_successors (m : ℕ)
    (hsucc : ∀ n : ℕ,
      injectiveSegalModel.categoryWithCofibrations.cofibrations
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n))) ∧
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
          ((discreteLengthSequence m).map (homOfLE (Nat.le_succ n)))) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((actualLeftAdjunction.{0}).unit.app
          ((simplicialYoneda.{0, 0} ReverseSimplex).obj
            (ReverseSimplex.mk m))) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((actualLeftAdjunction.{0}).unit.app
          ((simplicialYoneda.{0, 0} ReverseSimplex).obj
            (ReverseSimplex.mk m))) :=
  ⟨actualRepresentableUnit_cofibration m,
    actualRepresentableUnit_localWeak_of_successors m hsucc⟩

end

end DaggerModels.PartII.ClassifyingReduction
