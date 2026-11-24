import DaggerModelsPartII.FiniteLastVertexFactor

/-! Chains of vertices in a finite coefficient-time prism. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra DaggerNerveHomotopy DaggerSSetGluing
open DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.TimePrismChain

noncomputable section

/-- The product ordered vertex set of a coefficient-time prism. -/
abbrev Vertex (k n : ℕ) := Fin (k + 1) × Fin (n + 1)

/-- A chain meeting every coefficient level. Finiteness follows from `Vertex`. -/
structure Chain (k n : ℕ) where
  vertices : Set (Vertex k n)
  chain : IsChain (· ≤ ·) vertices
  covers : ∀ i : Fin (k + 1), ∃ j : Fin (n + 1), (i, j) ∈ vertices

/-- Every chain has a finite vertex set. -/
theorem Chain.finite_vertices {k n : ℕ} (A : Chain k n) : A.vertices.Finite :=
  Set.toFinite A.vertices

instance (k n : ℕ) : PartialOrder (Chain k n) where
  le A B := A.vertices ⊆ B.vertices
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ h h' := Set.Subset.trans h h'
  le_antisymm A B h h' := by
    cases A with
    | mk av ac acov =>
      cases B with
      | mk bv bc bcov =>
        congr 1
        exact Set.Subset.antisymm h h'

/-- Embed all earlier coefficient levels into the next prism. -/
def lowerVertex (k n : ℕ) : Vertex k n → Vertex (k + 1) n :=
  fun v ↦ (v.1.castSucc, v.2)

/-- The greatest vertex in the product order. -/
def topVertex (k n : ℕ) : Vertex k n := (Fin.last k, Fin.last n)

private theorem le_top (k n : ℕ) (v : Vertex k n) : v ≤ topVertex k n := by
  exact ⟨Fin.le_last _, Fin.le_last _⟩

/-- Add the greatest vertex; this is the upper leg of the contraction zigzag. -/
def addMax (k n : ℕ) (A : Chain k n) : Chain k n where
  vertices := insert (topVertex k n) A.vertices
  chain := A.chain.insert (by
    intro b hb hne
    exact Or.inr (le_top k n b))
  covers := by
    intro i
    obtain ⟨j, hj⟩ := A.covers i
    exact ⟨j, Set.mem_insert_of_mem _ hj⟩

theorem le_addMax (k n : ℕ) (A : Chain k n) : A ≤ addMax k n A :=
  Set.subset_insert _ _

theorem lowerVertex_injective (k n : ℕ) : Function.Injective (lowerVertex k n) := by
  intro a b h
  have hfirst : a.1.castSucc = b.1.castSucc := congrArg Prod.fst h
  have hsecond : a.2 = b.2 := congrArg (fun v : Vertex (k + 1) n ↦ v.2) h
  exact Prod.ext (Fin.castSucc_injective _ hfirst) hsecond

theorem lowerVertex_le_iff (k n : ℕ) (a b : Vertex k n) :
    lowerVertex k n a ≤ lowerVertex k n b ↔ a ≤ b := by
  simp [lowerVertex, Prod.le_def]

/-- Keep only vertices at earlier coefficient levels. -/
def restrict (k n : ℕ) (A : Chain (k + 1) n) : Chain k n where
  vertices := lowerVertex k n ⁻¹' A.vertices
  chain := IsChain.preimage (· ≤ ·) (· ≤ ·) (lowerVertex k n)
    (lowerVertex_injective k n) (by
      intro a b h
      exact (lowerVertex_le_iff k n a b).mp h) A.chain
  covers := by
    intro i
    obtain ⟨j, hj⟩ := A.covers i.castSucc
    exact ⟨j, hj⟩

/-- Add one greatest vertex above an earlier-level chain. -/
def extend (k n : ℕ) (A : Chain k n) : Chain (k + 1) n where
  vertices := insert (topVertex (k + 1) n) (lowerVertex k n '' A.vertices)
  chain := (IsChain.image (· ≤ ·) (· ≤ ·) (lowerVertex k n)
    (by intro a b h; exact (lowerVertex_le_iff k n a b).mpr h) A.chain).insert (by
      intro b hb hne
      exact Or.inr (le_top (k + 1) n b))
  covers := by
    intro i
    by_cases hi : i = Fin.last (k + 1)
    · subst i
      exact ⟨Fin.last n, Set.mem_insert _ _⟩
    · obtain ⟨a, ha⟩ := Fin.exists_castSucc_eq.mpr hi
      obtain ⟨j, hj⟩ := A.covers a
      exact ⟨j, Set.mem_insert_of_mem _ ⟨(a, j), hj, by simp [lowerVertex, ha]⟩⟩

theorem lowerVertex_ne_top (k n : ℕ) (a : Vertex k n) :
    lowerVertex k n a ≠ topVertex (k + 1) n := by
  intro h
  have := congrArg Prod.fst h
  exact (Fin.castSucc_ne_last a.1) this

theorem restrict_extend (k n : ℕ) (A : Chain k n) :
    restrict k n (extend k n A) = A := by
  cases A with
  | mk av ac acov =>
    have hv : (restrict k n (extend k n ⟨av, ac, acov⟩)).vertices = av := by
      ext v
      change lowerVertex k n v ∈ insert (topVertex (k + 1) n)
        (lowerVertex k n '' av) ↔ v ∈ av
      simp only [Set.mem_insert_iff, Set.mem_image]
      constructor
      · rintro (h | ⟨u, hu, huv⟩)
        · exact False.elim ((lowerVertex_ne_top k n v) h)
        · exact (lowerVertex_injective k n huv).symm ▸ hu
      · intro h
        exact Or.inr ⟨v, h, rfl⟩
    cases h : restrict k n (extend k n ⟨av, ac, acov⟩) with
    | mk rv rc rcov =>
      simp only [h] at hv
      cases hv
      rfl

theorem extend_restrict_le_addMax (k n : ℕ) (A : Chain (k + 1) n) :
    extend k n (restrict k n A) ≤ addMax (k + 1) n A := by
  intro v hv
  rcases hv with htop | ⟨u, hu, rfl⟩
  · exact Or.inl htop
  · exact Or.inr hu

/-- Inclusion of chains is preserved when the greatest vertex is added. -/
theorem addMax_monotone (k n : ℕ) : Monotone (addMax k n) := by
  intro A B h v hv
  rcases hv with htop | hA
  · exact Or.inl htop
  · exact Or.inr (h hA)

/-- Restriction preserves inclusion. -/
theorem restrict_monotone (k n : ℕ) : Monotone (restrict k n) := by
  intro A B h v hv
  exact h hv

/-- Extension preserves inclusion. -/
theorem extend_monotone (k n : ℕ) : Monotone (extend k n) := by
  intro A B h v hv
  rcases hv with htop | ⟨u, hu, rfl⟩
  · exact Or.inl htop
  · exact Or.inr ⟨u, h hu, rfl⟩

/-- The restriction functor from a larger prism to earlier coefficient levels. -/
def restrictFunctor (k n : ℕ) : Chain (k + 1) n ⥤ Chain k n :=
  (restrict_monotone k n).functor

/-- The extension functor adjoining the greatest vertex. -/
def extendFunctor (k n : ℕ) : Chain k n ⥤ Chain (k + 1) n :=
  (extend_monotone k n).functor

/-- The endofunctor that adjoins the greatest vertex. -/
def addMaxFunctor (k n : ℕ) : Chain k n ⥤ Chain k n :=
  (addMax_monotone k n).functor

/-- Every chain includes into its greatest-vertex extension. -/
def idToAddMax (k n : ℕ) : 𝟭 (Chain k n) ⟶ addMaxFunctor k n where
  app A := homOfLE (le_addMax k n A)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Extension after restriction includes into the greatest-vertex extension. -/
def extendRestrictToAddMax (k n : ℕ) :
    restrictFunctor k n ⋙ extendFunctor k n ⟶ addMaxFunctor (k + 1) n where
  app A := homOfLE (extend_restrict_le_addMax k n A)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Restricting an extended chain is the identity up to the canonical equality arrow. -/
def extendRestrictToId (k n : ℕ) :
    extendFunctor k n ⋙ restrictFunctor k n ⟶ 𝟭 (Chain k n) where
  app A := eqToHom (restrict_extend k n A)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Restriction induces a weak equivalence on nerves. -/
theorem restrict_geometricW (k n : ℕ) :
    SSet.KanComplex.W (TopCat.toSSet.map
      (SSet.toTop.map (nerveMap (restrictFunctor k n)))) := by
  apply nerveMap_geometricW (restrictFunctor k n) (extendFunctor k n)
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ ⟨extendRestrictToAddMax k n⟩)
      (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ ⟨idToAddMax (k + 1) n⟩))
  · exact Relation.EqvGen.rel _ _ ⟨extendRestrictToId k n⟩

/-- The earlier-coefficient restriction is a weak equivalence of simplicial sets. -/
theorem restrict_weak (k n : ℕ) :
    WeakEquivalence (nerveMap (restrictFunctor k n)) :=
  (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).mpr
    (restrict_geometricW k n)

/-- At one coefficient level all vertices form a chain. -/
def baseFull (n : ℕ) : Chain 0 n where
  vertices := Set.univ
  chain := by
    intro a _ b _ _
    rcases a with ⟨i, j⟩
    rcases b with ⟨i', j'⟩
    have hi : i = i' := by
      rw [Fin.eq_zero i, Fin.eq_zero i']
    subst i'
    rcases le_total j j' with h | h
    · exact Or.inl ⟨le_rfl, h⟩
    · exact Or.inr ⟨le_rfl, h⟩
  covers := by
    intro i
    exact ⟨0, Set.mem_univ _⟩

private theorem le_baseFull (n : ℕ) (A : Chain 0 n) : A ≤ baseFull n :=
  Set.subset_univ _

/-- The one-coefficient chain category has a greatest object. -/
def baseTerminal (n : ℕ) : IsTerminal (baseFull n) :=
  IsTerminal.ofUniqueHom (fun A ↦ homOfLE (le_baseFull n A))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- Weak contractibility of the one-coefficient chain poset. -/
theorem base_point_GW (n : ℕ) : GW (pointMap (nerve (Chain 0 n))) := by
  let E := Chain 0 n
  let e : E := baseFull n
  let he : IsTerminal e := baseTerminal n
  let collapse : E ⥤ Discrete PUnit.{1} := (Functor.const E).obj ⟨PUnit.unit⟩
  let center : Discrete PUnit.{1} ⥤ E := (Functor.const _).obj e
  let hE : 𝟭 E ⟶ collapse ⋙ center :=
    { app A := he.from A
      naturality _ _ _ := Subsingleton.elim _ _ }
  let hP : center ⋙ collapse ⟶ 𝟭 (Discrete PUnit.{1}) :=
    { app A := eqToHom (Subsingleton.elim _ _)
      naturality _ _ _ := Subsingleton.elim _ _ }
  have hw : WeakEquivalence (nerveMap collapse) := (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW collapse center
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hE⟩))
      (Relation.EqvGen.rel _ _ ⟨hP⟩))
  have hm : nerveMap collapse ≫
      (DaggerOriginalFlagFlankification.nerveDiscreteIso PUnit.{1}).hom =
      pointMap (nerve E) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← hm]
  infer_instance

/-- The nerve of the full-support chain poset is weakly contractible. -/
theorem point_GW (k n : ℕ) : GW (pointMap (nerve (Chain k n))) := by
  induction k with
  | zero => exact base_point_GW n
  | succ k ih =>
    have hr : WeakEquivalence (nerveMap (restrictFunctor k n)) := restrict_weak k n
    have hl : WeakEquivalence (pointMap (nerve (Chain k n))) :=
      (weakEquivalence_iff_GW _).mpr ih
    have hm : nerveMap (restrictFunctor k n) ≫ pointMap (nerve (Chain k n)) =
        pointMap (nerve (Chain (k + 1) n)) := pointIsTerminal.hom_ext _ _
    apply (weakEquivalence_iff_GW _).mp
    rw [← hm]
    infer_instance

end

end DaggerModels.PartII.TimePrismChain
