import DaggerModelsPartII.CosimplicialResolution
import DaggerModelsPartII.ReedyFibrantDiagrams
import DaggerModelsPartII.DiagramHomBoundaryLifting
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Localization.Construction
import TopCatModelCategory.ModelCategorySSet

/-! Homotopy invariance of the mapping simplicial sets of cosimplicial resolutions. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u v' u'

namespace DaggerModels.PartII

theorem map_weak_of_trivialFibration {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] [ModelCategory D] (F : C ⥤ D)
    (mapTF : ∀ {A B : C} (p : A ⟶ B), trivialFibrations C p → weakEquivalences D (F.map p))
    {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences D (F.map f) := by
  letI : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  let d := (inferInstance : Nonempty (FibrantBrownFactorization f)).some
  have hr := mapTF d.r (mem_trivialFibrations _)
  have hp := mapTF d.p (mem_trivialFibrations _)
  have hi : weakEquivalences D (F.map d.i) := by
    apply (weakEquivalences D).of_postcomp _ _ hr
    rw [← F.map_comp, d.i_r, F.map_id]
    exact (weakEquivalences D).id_mem _
  rw [← d.fac, F.map_comp]
  exact (weakEquivalences D).comp_mem _ _ hi hp

private theorem kanTrivialFibration_of_boundary {X Y : SSet.{v}} (f : X ⟶ Y)
    (h : ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{v} n).ι f) :
    trivialFibrations SSet.{v} f := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  intro A B i hi
  obtain ⟨n⟩ := hi
  exact h n

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance mappingInvarianceReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) :=
  simplicialReedyModelCategory C


namespace CosimplicialResolution

variable {X : C} (R : CosimplicialResolution X)

/-- The mapping simplicial set of a cosimplicial resolution sends trivial fibrations to
Kan trivial fibrations. -/
theorem mappingSSet_map_trivialFibration {Y Z : C} (p : Y ⟶ Z)
    (hp : trivialFibrations C p) : trivialFibrations SSet.{v} (R.mappingSSet.map p) := by
  letI := R.fibrantOp
  apply kanTrivialFibration_of_boundary
  intro n
  change HasLiftingProperty (SSet.boundary n).ι (diagramHomPrecomp p.op R.oppositeDiagram)
  apply diagramHomPrecomp_boundary_lifting
  have hi : trivialCofibrations Cᵒᵖ p.op := by
    rw [trivialCofibrations_op]
    exact hp
  exact hasLiftingProperty_of_wfs p.op _ hi
    ((reedyFibrant_iff_matchingComparison R.oppositeDiagram).mp R.fibrantOp n)

/-- In the target variable the mapping simplicial set preserves weak equivalences between
fibrant objects. -/
theorem mappingSSet_map_weak {Y Z : C} [IsFibrant Y] [IsFibrant Z] (p : Y ⟶ Z)
    (hp : weakEquivalences C p) : weakEquivalences SSet.{v} (R.mappingSSet.map p) :=
  map_weak_of_trivialFibration R.mappingSSet
    (fun f hf ↦ (R.mappingSSet_map_trivialFibration f hf).2) p hp

omit [HasColimitsOfSize.{0, 0} C] in
private theorem oppositeInitialTo_mem_cofibrations (Z : C) [IsFibrant Z] :
    cofibrations Cᵒᵖ (initial.to (op Z)) := by
  rw [cofibrations_op]
  exact (fibration_iff _).mp
    ((isFibrant_iff_of_isTerminal (initial.to (op Z)).unop (terminalUnopOfInitial initialIsInitial)).mp inferInstance)

def mappingFromOppositeDiagram (Z : C) :
    (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) ⥤ SSet.{v} :=
  (Functor.whiskeringRight _ _ _).obj (coyoneda.obj (op (op Z)))

theorem mappingFromOppositeDiagram_map_trivialFibration (Z : C) [IsFibrant Z]
    {W V : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ} (f : W ⟶ V)
    (hf : trivialFibrations (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) f) :
    trivialFibrations SSet.{v} ((mappingFromOppositeDiagram Z).map f) := by
  have h : reedyMatchingProperty (trivialFibrations Cᵒᵖ) f := by
    rw [← simplicialReedyFibrations_inf_weakEquivalences]
    exact hf
  apply kanTrivialFibration_of_boundary
  intro n
  change HasLiftingProperty (SSet.boundary n).ι (diagramHomPostcomp (op Z) f)
  apply diagramHomPostcomp_boundary_lifting
  exact hasLiftingProperty_of_wfs _ _ (oppositeInitialTo_mem_cofibrations Z) (h n)

namespace Comparison

variable {R} {Y : C} {S : CosimplicialResolution Y} {f : X ⟶ Y}

/-- In the source variable any comparison over a weak equivalence induces a Kan weak
equivalence when the target is fibrant. -/
theorem precomp_weak (g : Comparison R S f) (hf : weakEquivalences C f)
    (Z : C) [IsFibrant Z] : weakEquivalences SSet.{v} (g.precomp Z) := by
  letI := R.fibrantOp
  letI := S.fibrantOp
  have h : weakEquivalences (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) g.mapOp := by
    intro n
    change weakEquivalences Cᵒᵖ (g.mapOp.app n)
    rw [weakEquivalences_op]
    exact g.levelwise_weak hf n
  exact map_weak_of_trivialFibration (mappingFromOppositeDiagram Z)
    (fun p hp ↦ (mappingFromOppositeDiagram_map_trivialFibration Z p hp).2) g.mapOp h

private theorem exists_comparison_path (g h : Comparison R S f) :
    ∃ (P : PathObject R.oppositeDiagram) (_ : P.IsVeryGood)
      (q : S.oppositeDiagram ⟶ P.P), q ≫ P.p₀ = g.mapOp ∧ q ≫ P.p₁ = h.mapOp := by
  letI := R.fibrantOp
  let P := (PathObject.exists_very_good R.oppositeDiagram).choose
  letI : P.IsVeryGood := (PathObject.exists_very_good R.oppositeDiagram).choose_spec
  let a := S.augmentationOp ≫ g.mapOp
  let b := prod.lift g.mapOp h.mapOp
  have ha : a = S.augmentationOp ≫ h.mapOp := g.comm.trans h.comm.symm
  have sq : CommSq (a ≫ P.ι) S.augmentationOp P.p b := by
    constructor
    apply prod.hom_ext
    · simp only [Category.assoc, P.p_fst, P.ι_p₀, Category.comp_id, b, prod.lift_fst]
      rfl
    · simp only [Category.assoc, P.p_snd, P.ι_p₁, Category.comp_id, b, prod.lift_snd]
      exact ha
  letI : HasLiftingProperty S.augmentationOp P.p :=
    hasLiftingProperty_of_wfs _ _ S.augmentationOp_mem (mem_fibrations _)
  have hg : sq.lift ≫ P.p₀ = g.mapOp := by
    rw [← P.p_fst, ← Category.assoc, sq.fac_right]
    exact prod.lift_fst _ _
  have hh : sq.lift ≫ P.p₁ = h.mapOp := by
    rw [← P.p_snd, ← Category.assoc, sq.fac_right]
    exact prod.lift_snd _ _
  exact ⟨P, inferInstance, sq.lift, hg, hh⟩

/-- The weak-equivalence test is independent of the lift between fixed resolutions. -/
theorem precomp_weak_iff_of_same_resolutions (g h : Comparison R S f)
    (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (g.precomp Z) ↔ weakEquivalences SSet.{v} (h.precomp Z) := by
  letI := R.fibrantOp
  obtain ⟨P, hP, q, hg, hh⟩ := exists_comparison_path g h
  letI := hP
  let F := mappingFromOppositeDiagram Z
  have h₀ : weakEquivalences SSet.{v} (F.map P.p₀) :=
    (mappingFromOppositeDiagram_map_trivialFibration Z P.p₀ (mem_trivialFibrations _)).2
  have h₁ : weakEquivalences SSet.{v} (F.map P.p₁) :=
    (mappingFromOppositeDiagram_map_trivialFibration Z P.p₁ (mem_trivialFibrations _)).2
  change weakEquivalences SSet.{v} (F.map g.mapOp) ↔
    weakEquivalences SSet.{v} (F.map h.mapOp)
  rw [← hg, ← hh, F.map_comp, F.map_comp]
  constructor
  · intro hw
    exact (weakEquivalences SSet.{v}).comp_mem _ _ ((weakEquivalences _).of_postcomp _ _ h₀ hw) h₁
  · intro hw
    exact (weakEquivalences SSet.{v}).comp_mem _ _ ((weakEquivalences _).of_postcomp _ _ h₁ hw) h₀

/-- Two comparisons over the same source map agree after localizing at Kan weak equivalences. -/
theorem precomp_localized_eq (g h : Comparison R S f) (Z : C) [IsFibrant Z] :
    (weakEquivalences SSet.{v}).Q.map (g.precomp Z) =
      (weakEquivalences SSet.{v}).Q.map (h.precomp Z) := by
  letI := R.fibrantOp
  obtain ⟨P, hP, q, hg, hh⟩ := exists_comparison_path g h
  letI := hP
  let F := mappingFromOppositeDiagram Z ⋙ (weakEquivalences SSet.{v}).Q
  have h₀ : F.map P.ι ≫ F.map P.p₀ = 𝟙 _ := by rw [← F.map_comp, P.ι_p₀, F.map_id]
  have h₁ : F.map P.ι ≫ F.map P.p₁ = 𝟙 _ := by rw [← F.map_comp, P.ι_p₁, F.map_id]
  haveI : IsIso (F.map P.p₀) :=
    (weakEquivalences SSet.{v}).Q_inverts _
      (mappingFromOppositeDiagram_map_trivialFibration Z P.p₀ (mem_trivialFibrations _)).2
  haveI : IsIso (F.map P.ι ≫ F.map P.p₀) := by rw [h₀]; infer_instance
  haveI : IsIso (F.map P.ι) := IsIso.of_isIso_comp_right _ (F.map P.p₀)
  have he : F.map P.p₀ = F.map P.p₁ := (cancel_epi (F.map P.ι)).mp (h₀.trans h₁.symm)
  change F.map g.mapOp = F.map h.mapOp
  rw [← hg, ← hh, F.map_comp, F.map_comp, he]

/-- The weak-equivalence test is independent of both resolutions and the comparison. -/
theorem precomp_weak_iff {R' : CosimplicialResolution X} {S' : CosimplicialResolution Y}
    (g : Comparison R S f) (g' : Comparison R' S' f) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (g.precomp Z) ↔ weakEquivalences SSet.{v} (g'.precomp Z) := by
  let r := R.comparison R' (𝟙 X)
  let s := S'.comparison S (𝟙 Y)
  let h : Comparison R S f :=
    { mapOp := s.mapOp ≫ g'.mapOp ≫ r.mapOp
      comm := by
        rw [← Category.assoc, s.comm, Category.assoc, ← Category.assoc S'.augmentationOp,
          g'.comm]
        simp only [Category.assoc, r.comm, CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.id_comp] }
  have hr := r.precomp_weak ((weakEquivalences C).id_mem _) Z
  have hs := s.precomp_weak ((weakEquivalences C).id_mem _) Z
  rw [g.precomp_weak_iff_of_same_resolutions h Z]
  let F := mappingFromOppositeDiagram Z
  change weakEquivalences SSet.{v} (F.map (s.mapOp ≫ g'.mapOp ≫ r.mapOp)) ↔
    weakEquivalences SSet.{v} (F.map g'.mapOp)
  rw [F.map_comp, F.map_comp]
  constructor
  · intro hw
    apply (weakEquivalences SSet.{v}).of_postcomp _ _ hr
    exact (weakEquivalences SSet.{v}).of_precomp _ _ hs hw
  · intro hw
    exact (weakEquivalences SSet.{v}).comp_mem _ _ hs
      ((weakEquivalences SSet.{v}).comp_mem _ _ hw hr)

/-- Composition of comparisons reverses the order of the source maps. -/
def comp {T : C} {U : CosimplicialResolution T} {k : Y ⟶ T}
    (g : Comparison R S f) (h : Comparison S U k) : Comparison R U (f ≫ k) where
  mapOp := h.mapOp ≫ g.mapOp
  comm := by
    rw [← Category.assoc, h.comm, Category.assoc, g.comm, CategoryTheory.op_comp,
      CategoryTheory.Functor.map_comp, Category.assoc]

/-- Precomposition by the composite comparison is the composite simplicial map. -/
theorem precomp_comp {T : C} {U : CosimplicialResolution T} {k : Y ⟶ T}
    (g : Comparison R S f) (h : Comparison S U k) (Z : C) :
    (g.comp h).precomp Z = h.precomp Z ≫ g.precomp Z :=
  (mappingFromOppositeDiagram Z).map_comp h.mapOp g.mapOp

end Comparison

end CosimplicialResolution

end

end DaggerModels.PartII
