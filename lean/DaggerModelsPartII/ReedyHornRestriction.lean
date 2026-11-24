import DaggerModelsPartII.DiagramRestrictionFibration
import DaggerModelsPartII.DiagramRestrictionLimits
import DaggerModelsPartII.ReedyFibrantDiagrams
import DaggerModelsPartII.SimplexFacetUnion
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Horn restrictions for homotopically constant Reedy fibrant diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty HomotopicalAlgebra

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, v} C] [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance hornRestrictionReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) :=
  simplicialReedyModelCategory C

local instance hornRestrictionTrivialFibrationsBaseChange :
    (trivialFibrations C).IsStableUnderBaseChange := by
  rw [← rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)]
  infer_instance

private def diagramRestriction_terminal (K : SSet.{v}) :
    IsTerminal (diagramRestriction K (⊤_ (SimplexCategoryᵒᵖ ⥤ C))) := by
  let F : (SimplexCategoryᵒᵖ ⥤ C) ⥤ C :=
    (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π K) ⋙ lim
  letI : PreservesLimit (Functor.empty.{0} _) F := by dsimp [F]; infer_instance
  exact terminalIsTerminal.isTerminalObj F _

/-- Restriction of a Reedy fibrant diagram along a monomorphism is a fibration. -/
theorem diagramRestrictionPre_fibration (W : SimplexCategoryᵒᵖ ⥤ C) [IsFibrant W]
    {K L : SSet.{v}} (j : K ⟶ L) [Mono j] :
    fibrations C (diagramRestrictionPre j W) := by
  let f := terminal.from W
  have hf : reedyMatchingProperty (fibrations C) f := mem_fibrations f
  haveI : IsIso (diagramRestrictionPre j (⊤_ (SimplexCategoryᵒᵖ ⥤ C))) :=
    isIso_of_isTerminal (diagramRestriction_terminal L) (diagramRestriction_terminal K) _
  let π := pullback.fst (diagramRestrictionPost K f) (diagramRestrictionPre j _)
  haveI : IsIso π := pullback_fst_iso_of_right_iso _ _
  have hπ : diagramRestrictionRelative j f ≫ π = diagramRestrictionPre j W :=
    pullback.lift_fst _ _ _
  rw [← hπ]
  exact ((fibrations C).cancel_right_of_respectsIso _ π).mpr
    (diagramRestrictionRelative_fibration j f hf)

variable (W : SimplexCategoryᵒᵖ ⥤ C) [IsFibrant W]
  (hW : ∀ {s t : SimplexCategoryᵒᵖ} (f : s ⟶ t), weakEquivalences C (W.map f))

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] [IsFibrant W] in
include hW in
private theorem facet_restriction_weak {n : ℕ} (i : Fin (n + 2)) :
    weakEquivalences C (diagramRestrictionPre (SSet.stdSimplex.face.{v} {i}ᶜ).ι W) := by
  let F := diagramRestrictionFunctor W
  let e := SSet.stdSimplex.faceSingletonComplIso.{v} i
  have he : IsIso (diagramRestrictionPre e.hom W) := inferInstanceAs (IsIso (F.map e.hom.op))
  have h : weakEquivalences C (diagramRestrictionPre (SSet.stdSimplex.δ.{v} i) W) := by
    apply ((weakEquivalences C).cancel_right_of_respectsIso _ (diagramRestrictionSimplexIso W n).hom).mp
    rw [show SSet.stdSimplex.δ.{v} i = SSet.stdSimplex.map (SimplexCategory.δ i) from rfl,
      diagramRestrictionSimplexIso_natural]
    exact ((weakEquivalences C).cancel_left_of_respectsIso _ _).mpr (hW _)
  rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι] at h
  change weakEquivalences C (F.map (e.hom ≫ (SSet.stdSimplex.face {i}ᶜ).ι).op) at h
  rw [op_comp, F.map_comp] at h
  exact ((weakEquivalences C).cancel_right_of_respectsIso _ (diagramRestrictionPre e.hom W)).mp h

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] [IsFibrant W] in
private theorem attach_restriction_trivial {n : ℕ} (i : Fin (n + 2))
    (S : Finset (Fin (n + 1)))
    (h : trivialFibrations C (diagramRestrictionPre (simplexFacetUnion.{v} n S).ι W)) :
    trivialFibrations C (diagramRestrictionPre
      (SSet.Subcomplex.homOfLE (simplexFacetUnion_attach.{v} i S).le₂₄) W) := by
  let sq := simplexFacetUnion_attach.{v} i S
  let A := simplexFacetUnion.{v} n S
  let a := SSet.Subcomplex.homOfLE sq.le₁₃
  let e := A.toImage (SSet.stdSimplex.δ i)
  let d := (SSet.stdSimplex.faceSingletonComplIso.{v} i).hom
  haveI : Mono e := mono_of_mono_fac (SSet.Subcomplex.toImage_ι A _)
  haveI : Epi e := inferInstanceAs (Epi (A.toImage _))
  haveI : IsIso e := isIso_of_mono_of_epi e
  have comm : e ≫ a = A.ι ≫ d := by
    apply (cancel_mono (SSet.stdSimplex.face.{v} {i}ᶜ).ι).mp
    rw [Category.assoc, Category.assoc, SSet.Subcomplex.homOfLE_ι]
    change A.toImage (SSet.stdSimplex.δ i) ≫ (A.image (SSet.stdSimplex.δ i)).ι = _
    rw [SSet.Subcomplex.toImage_ι, SSet.stdSimplex.faceSingletonComplIso_hom_ι]
  let F := diagramRestrictionFunctor W
  have w := congrArg (fun k ↦ F.map k.op) comm
  simp only [op_comp, F.map_comp] at w
  have h' : trivialFibrations C (F.map a.op) := by
    apply ((trivialFibrations C).cancel_right_of_respectsIso _ (F.map e.op)).mp
    rw [w]
    exact ((trivialFibrations C).cancel_left_of_respectsIso (F.map d.op) _).mpr h
  exact (trivialFibrations C).of_isPullback (diagramRestriction_isPullback W sq.isPushout).flip h'

private theorem facetUnion_singleton {n : ℕ} (i : Fin (n + 1)) :
    simplexFacetUnion.{v} n {i} = SSet.stdSimplex.face {i}ᶜ := by
  rw [← Finset.insert_empty, simplexFacetUnion_insert]
  simp [simplexFacetUnion]

include hW in
/-- Restriction to any nonempty proper union of facets is a trivial fibration. -/
theorem diagramRestrictionPre_facetUnion_trivial (n : ℕ) :
    ∀ (S : Finset (Fin (n + 1))), S.Nonempty → S ≠ Finset.univ →
      trivialFibrations C (diagramRestrictionPre (simplexFacetUnion.{v} n S).ι W) := by
  induction n with
  | zero =>
    intro S hS hn
    obtain ⟨i, hi⟩ := hS
    exact (hn (Finset.eq_univ_of_forall (fun j ↦ ((Fin.eq_zero i).trans (Fin.eq_zero j).symm) ▸ hi))).elim
  | succ n ih =>
    let F := diagramRestrictionFunctor W
    have aux (S : Finset (Fin (n + 2))) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
        ∃ (i : Fin (n + 2))
          (a : (SSet.stdSimplex.face.{v} {i}ᶜ).toSSet ⟶ (simplexFacetUnion (n + 1) S).toSSet),
          a ≫ (simplexFacetUnion (n + 1) S).ι = (SSet.stdSimplex.face {i}ᶜ).ι ∧
          trivialFibrations C (F.map a.op) := by
      induction S using Finset.induction_on with
      | empty => exact (Finset.not_nonempty_empty hne).elim
      | insert j S hj ind =>
        by_cases hs : S.Nonempty
        · have hs' : S ≠ Finset.univ := fun h ↦ hj (h ▸ Finset.mem_univ j)
          obtain ⟨i, a, ha, ha'⟩ := ind hs hs'
          let T := Finset.univ.filter (fun k : Fin (n + 1) ↦ j.succAbove k ∈ S)
          have hTS : T.image j.succAbove = S := by
            ext k
            constructor
            · intro hk
              obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
              exact (Finset.mem_filter.mp hl).2
            · intro hk
              have hkj : k ≠ j := fun e ↦ hj (e ▸ hk)
              obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hkj
              exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
          have ht : T.Nonempty := by
            rw [← hTS, Finset.image_nonempty] at hs
            exact hs
          have ht' : T ≠ Finset.univ := by
            intro h
            apply hproper
            apply Finset.eq_univ_of_forall
            intro k
            by_cases hk : k = j
            · exact Finset.mem_insert.mpr (Or.inl hk)
            · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
              exact Finset.mem_insert_of_mem (hTS ▸ Finset.mem_image_of_mem _
                (h.symm ▸ Finset.mem_univ l))
          have hex : ∃ b : (simplexFacetUnion.{v} (n + 1) S).toSSet ⟶
              (simplexFacetUnion (n + 1) (insert j S)).toSSet,
              b ≫ (simplexFacetUnion (n + 1) (insert j S)).ι =
                (simplexFacetUnion (n + 1) S).ι ∧ trivialFibrations C (F.map b.op) := by
            rw [← hTS]
            let sq := simplexFacetUnion_attach.{v} j T
            exact ⟨SSet.Subcomplex.homOfLE sq.le₂₄, SSet.Subcomplex.homOfLE_ι _,
              attach_restriction_trivial W j T (ih T ht ht')⟩
          obtain ⟨b, hb, hb'⟩ := hex
          refine ⟨i, a ≫ b, ?_, ?_⟩
          · rw [Category.assoc, hb]
            exact ha
          · rw [op_comp, F.map_comp]
            exact (trivialFibrations C).comp_mem _ _ hb' ha'
        · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.insert_empty]
          let e := SSet.Subcomplex.toSSetFunctor.mapIso (eqToIso (facetUnion_singleton j).symm)
          refine ⟨j, e.hom, ?_, ?_⟩
          · exact SSet.Subcomplex.homOfLE_ι (le_of_eq (facetUnion_singleton j).symm)
          · exact (trivialFibrations C).of_isIso _
    intro S hs ht
    obtain ⟨i, a, ha, ha'⟩ := aux S hs ht
    refine ⟨diagramRestrictionPre_fibration W _, ?_⟩
    have hh := facet_restriction_weak W hW i
    change weakEquivalences C (F.map (SSet.stdSimplex.face.{v} {i}ᶜ).ι.op) at hh
    rw [← ha, op_comp, F.map_comp] at hh
    exact (weakEquivalences C).of_postcomp _ _ ha'.2 hh

include hW in
/-- A horn restriction of a homotopically constant Reedy fibrant diagram is trivial. -/
theorem diagramRestrictionPre_horn_trivial (n : ℕ) (i : Fin (n + 2)) :
    trivialFibrations C (diagramRestrictionPre (SSet.horn.{v} (n + 1) i).ι W) := by
  rw [← simplexFacetUnion_compl_singleton]
  apply diagramRestrictionPre_facetUnion_trivial W hW
  · refine ⟨i.succAbove 0, ?_⟩
    exact Finset.mem_compl.mpr (by simp)
  · intro h
    have hi : i ∈ ({i}ᶜ : Finset (Fin (n + 2))) := h.symm ▸ Finset.mem_univ i
    simp at hi

include hW in
/-- Relative horn restrictions between homotopically constant fibrant diagrams are trivial. -/
theorem diagramRestrictionRelative_horn_trivial {V : SimplexCategoryᵒᵖ ⥤ C} [IsFibrant V]
    (hV : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t), weakEquivalences C (V.map g))
    (f : W ⟶ V) (hf : reedyMatchingProperty (fibrations C) f)
    (n : ℕ) (i : Fin (n + 2)) :
    trivialFibrations C (diagramRestrictionRelative (SSet.horn.{v} (n + 1) i).ι f) := by
  let K := SSet.horn.{v} (n + 1) i
  let π := pullback.fst (diagramRestrictionPost K.toSSet f) (diagramRestrictionPre K.ι V)
  have hπ : trivialFibrations C π :=
    (trivialFibrations C).pullback_fst _ _ (diagramRestrictionPre_horn_trivial V hV n i)
  have hw : weakEquivalences C (diagramRestrictionRelative K.ι f ≫ π) := by
    change weakEquivalences C (pullback.lift _ _ _ ≫ pullback.fst _ _)
    rw [pullback.lift_fst]
    exact (diagramRestrictionPre_horn_trivial W hW n i).2
  exact ⟨diagramRestrictionRelative_fibration K.ι f hf,
    (weakEquivalences C).of_postcomp _ _ hπ.2 hw⟩

end

end DaggerModels.PartII
