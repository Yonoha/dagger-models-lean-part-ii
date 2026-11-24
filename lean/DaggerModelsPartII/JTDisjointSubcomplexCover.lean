import DaggerModelsPartII.JTFiniteSubcomplexPreimageGluing

/-!
# Descent and preimage comparison for disjoint simplicial subcomplexes
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u v

namespace DaggerModels.PartII.JTDisjointSubcomplexCover

open SSet.Subcomplex

noncomputable section

variable {K X : SSet.{u}} {ι : Type v} (A : ι → K.Subcomplex)

/-- The standard subcomplex cover by all members and their actual intersections. -/
def cover : MulticoequalizerDiagram (⨆ i, A i) A (fun i j ↦ A i ⊓ A j) :=
  ⟨rfl, fun _ _ ↦ rfl⟩

abbrev inclusion (i : ι) : (A i).toSSet ⟶ (⨆ j, A j : K.Subcomplex).toSSet :=
  SSet.Subcomplex.homOfLE (le_iSup A i)

/-- To compare maps on the union, it suffices to compare their full restrictions. -/
theorem hom_ext {f g : (⨆ i, A i : K.Subcomplex).toSSet ⟶ X}
    (H : ∀ i, inclusion A i ≫ f = inclusion A i ≫ g) : f = g := by
  apply Multicofork.IsColimit.hom_ext (cover A).isColimit
  exact H

/-- Descend maps on a cover that agree on every actual pairwise intersection. -/
def glueCompatible (g : ∀ i, (A i).toSSet ⟶ X)
    (h : ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : A i ⊓ A j ≤ A i) ≫ g i =
      SSet.Subcomplex.homOfLE (inf_le_right : A i ⊓ A j ≤ A j) ≫ g j) :
    (⨆ i, A i : K.Subcomplex).toSSet ⟶ X :=
  Multicofork.IsColimit.desc (cover A).isColimit g (fun p ↦ h p.1 p.2)

@[reassoc]
theorem inclusion_glueCompatible (g : ∀ i, (A i).toSSet ⟶ X)
    (h : ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : A i ⊓ A j ≤ A i) ≫ g i =
      SSet.Subcomplex.homOfLE (inf_le_right : A i ⊓ A j ≤ A j) ≫ g j) (i : ι) :
    inclusion A i ≫ glueCompatible A g h = g i :=
  Multicofork.IsColimit.fac (cover A).isColimit _ _ i

private theorem overlap
    (hd : Pairwise fun i j ↦ A i ⊓ A j = ⊥) (g : ∀ i, (A i).toSSet ⟶ X) (i j : ι) :
    SSet.Subcomplex.homOfLE (inf_le_left : A i ⊓ A j ≤ A i) ≫ g i =
      SSet.Subcomplex.homOfLE (inf_le_right : A i ⊓ A j ≤ A j) ≫ g j := by
  by_cases hij : i = j
  · subst j
    rfl
  · exact (isInitialBot.ofIso (SSet.Subcomplex.eqToIso (hd hij).symm)).hom_ext _ _

/-- Arbitrary maps on disjoint members descend to their full union. -/
def glue (hd : Pairwise fun i j ↦ A i ⊓ A j = ⊥) (g : ∀ i, (A i).toSSet ⟶ X) :
    (⨆ i, A i : K.Subcomplex).toSSet ⟶ X :=
  glueCompatible A g (overlap A hd g)

@[reassoc]
theorem inclusion_glue (hd : Pairwise fun i j ↦ A i ⊓ A j = ⊥)
    (g : ∀ i, (A i).toSSet ⟶ X) (i : ι) :
    inclusion A i ≫ glue A hd g = g i :=
  inclusion_glueCompatible A g (overlap A hd g) i

/-- The original monomorphisms are the actual restrictions to their images. -/
def rangeLeg {Y : ι → SSet.{u}} (f : ∀ i, Y i ⟶ K) (i : ι) :
    Y i ⟶ (⨆ j, range (f j) : K.Subcomplex).toSSet :=
  toRange (f i) ≫ inclusion (fun j ↦ range (f j)) i

@[reassoc (attr := simp)]
theorem rangeLeg_ι {Y : ι → SSet.{u}} (f : ∀ i, Y i ⟶ K) (i : ι) :
    rangeLeg f i ≫ (⨆ j, range (f j) : K.Subcomplex).ι = f i := by
  simp [rangeLeg]

theorem exists_glue_ranges {Y : ι → SSet.{u}} (f : ∀ i, Y i ⟶ K) [∀ i, Mono (f i)]
    (hd : Pairwise fun i j ↦ range (f i) ⊓ range (f j) = ⊥) (g : ∀ i, Y i ⟶ X) :
    ∃ G : (⨆ j, range (f j) : K.Subcomplex).toSSet ⟶ X, ∀ i, rangeLeg f i ≫ G = g i := by
  refine ⟨glue (fun j ↦ range (f j)) hd (fun i ↦ inv (toRange (f i)) ≫ g i), ?_⟩
  intro i
  simp only [rangeLeg, Category.assoc, inclusion_glue, IsIso.hom_inv_id_assoc]

/-- Weak equivalences on a disjoint finite cover suffice for the actual
comparison of the union with its preimage. -/
theorem preimage_weak [Fintype ι] (f : X ⟶ K) (hd : Pairwise fun i j ↦ A i ⊓ A j = ⊥)
    (h : ∀ i, WeakEquivalence ((A i).fromPreimage f)) :
    WeakEquivalence ((⨆ i, A i : K.Subcomplex).fromPreimage f) := by
  classical
  rw [← Finset.sup_univ_eq_iSup]
  apply JTFiniteSubcomplexPreimageGluing.weak_finset_sup
  intro t _ ht
  obtain ⟨i, hi⟩ := ht
  by_cases hs : t = {i}
  · subst t
    have he : (({i} : Finset ι).inf fun j ↦ A j) = A i := Finset.inf_singleton
    rw [he]
    exact h i
  · obtain ⟨j, hj, hji⟩ : ∃ j ∈ t, j ≠ i := by
      by_contra! H
      exact hs (Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, H⟩)
    have htbot : t.inf A = ⊥ := by
      apply le_antisymm _ bot_le
      exact (le_inf (Finset.inf_le hi) (Finset.inf_le hj)).trans_eq (hd hji.symm)
    rw [htbot]
    let h₀ : IsInitial (((⊥ : K.Subcomplex).preimage f) : SSet.{u}) := isInitialBot
    have he : (⊥ : K.Subcomplex).fromPreimage f = (h₀.uniqueUpToIso isInitialBot).hom :=
      h₀.hom_ext _ _
    rw [he]
    infer_instance

end

end DaggerModels.PartII.JTDisjointSubcomplexCover
