import DaggerModelsPartII.TimePrismChain

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra DaggerNerveHomotopy DaggerSSetGluing
open DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.TimePrismChainRelative

noncomputable section

open TimePrismChain

/-- Full-support chains containing a prescribed partial chain, with bounded times. -/
structure Chain (k n : ℕ) (U : Set (Vertex k n)) (b : Fin (n + 1)) where
  toChain : TimePrismChain.Chain k n
  contains : U ⊆ toChain.vertices
  bounded : ∀ v ∈ toChain.vertices, v.2 ≤ b

/-- The relative chain has finitely many vertices. -/
theorem Chain.finite_vertices {k n : ℕ} {U : Set (Vertex k n)}
    {b : Fin (n + 1)} (A : Chain k n U b) : A.toChain.vertices.Finite :=
  A.toChain.finite_vertices

instance (k n : ℕ) (U : Set (Vertex k n)) (b : Fin (n + 1)) :
    PartialOrder (Chain k n U b) where
  le A B := A.toChain ≤ B.toChain
  le_refl _ := le_refl _
  le_trans _ _ _ h h' := le_trans h h'
  le_antisymm A B h h' := by
    cases A with
    | mk av ac ab =>
      cases B with
      | mk bv bc bb =>
        congr 1
        exact le_antisymm h h'

/-- The least time required at the final coefficient level, capped by `b`. -/
def cut (k n : ℕ) (U : Set (Vertex (k + 1) n)) (b : Fin (n + 1)) : Fin (n + 1) :=
  b ⊓ sInf {j | (Fin.last (k + 1), j) ∈ U}

private theorem cut_le (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) : cut k n U b ≤ b := inf_le_left

private theorem cut_le_last (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b j : Fin (n + 1)) (hj : (Fin.last (k + 1), j) ∈ U) :
    cut k n U b ≤ j :=
  (inf_le_right).trans (sInf_le hj)

/-- The prescribed chain on earlier coefficient levels. -/
def lower (k n : ℕ) (U : Set (Vertex (k + 1) n)) : Set (Vertex k n) :=
  lowerVertex k n ⁻¹' U

/-- Prescribed vertices at the final coefficient level. -/
def final (k n : ℕ) (U : Set (Vertex (k + 1) n)) : Set (Vertex (k + 1) n) :=
  {v | v ∈ U ∧ v.1 = Fin.last (k + 1)}

private theorem lower_time_le_final (k n : ℕ)
    {S : Set (Vertex (k + 1) n)} (hS : IsChain (· ≤ ·) S)
    {a : Vertex k n} {j : Fin (n + 1)}
    (ha : lowerVertex k n a ∈ S) (hj : (Fin.last (k + 1), j) ∈ S) : a.2 ≤ j := by
  have hne : lowerVertex k n a ≠ (Fin.last (k + 1), j) := by
    intro h
    have hc := congrArg Prod.fst h
    exact (Fin.castSucc_ne_last a.1) hc
  rcases hS ha hj hne with h | h
  · exact h.2
  · exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last a.1)) h.1)

private theorem lower_bounded (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hb : ∀ v ∈ U, v.2 ≤ b) {a : Vertex k n}
    (ha : a ∈ lower k n U) : a.2 ≤ cut k n U b := by
  apply le_inf
  · exact hb (lowerVertex k n a) ha
  · apply le_sInf
    intro j hj
    exact lower_time_le_final k n hU ha hj

/-- Restrict a full-support chain to earlier coefficient levels. -/
def restrict (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (A : Chain (k + 1) n U b) :
    Chain k n (lower k n U) (cut k n U b) where
  toChain := TimePrismChain.restrict k n A.toChain
  contains := fun _ h ↦ A.contains h
  bounded := by
    intro v hv
    apply le_inf
    · exact A.bounded (lowerVertex k n v) hv
    · apply le_sInf
      intro j hj
      exact lower_time_le_final k n A.toChain.chain hv (A.contains hj)

/-- Extend an earlier-level chain by the prescribed final vertices and the bounded top. -/
def extend (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b)
    (A : Chain k n (lower k n U) (cut k n U b)) : Chain (k + 1) n U b where
  toChain := {
    vertices := insert (Fin.last (k + 1), b)
      ((lowerVertex k n '' A.toChain.vertices) ∪ final k n U)
    chain := by
      apply IsChain.insert
      · apply isChain_union.mpr
        refine ⟨?_, ?_, ?_⟩
        · exact IsChain.image (· ≤ ·) (· ≤ ·) (lowerVertex k n)
            (by intro a c hac; exact (lowerVertex_le_iff k n a c).mpr hac)
            A.toChain.chain
        · exact hU.mono (by intro v hv; exact hv.1)
        · intro a ha c hc _
          obtain ⟨v, hv, rfl⟩ := ha
          have hcv : (Fin.last (k + 1), c.2) ∈ U := by
            convert hc.1 using 1
            exact Prod.ext hc.2.symm rfl
          have htime : v.2 ≤ c.2 := (A.bounded v hv).trans
            (cut_le_last k n U b c.2 hcv)
          exact Or.inl ⟨by simpa [lowerVertex, hc.2] using Fin.le_last v.1.castSucc, htime⟩
      · intro v hv _
        rcases hv with himg | hfinal
        · obtain ⟨a, ha, rfl⟩ := himg
          exact Or.inr ⟨Fin.le_last _, (A.bounded a ha).trans (cut_le k n U b)⟩
        · exact Or.inr ⟨Fin.le_last _, hUb v hfinal.1⟩
    covers := by
      intro i
      by_cases hi : i = Fin.last (k + 1)
      · subst i
        exact ⟨b, Set.mem_insert _ _⟩
      · obtain ⟨a, ha⟩ := Fin.exists_castSucc_eq.mpr hi
        obtain ⟨j, hj⟩ := A.toChain.covers a
        exact ⟨j, Set.mem_insert_of_mem _ (Or.inl
          ⟨(a, j), hj, by simp [lowerVertex, ha]⟩)⟩ }
  contains := by
    intro v hv
    by_cases hlast : v.1 = Fin.last (k + 1)
    · exact Set.mem_insert_of_mem _ (Or.inr ⟨hv, hlast⟩)
    · obtain ⟨a, ha⟩ := Fin.exists_castSucc_eq.mpr hlast
      have hlow : (a, v.2) ∈ lower k n U := by
        simpa [lower, lowerVertex, ha] using hv
      exact Set.mem_insert_of_mem _ (Or.inl
        ⟨(a, v.2), A.contains hlow, by simp [lowerVertex, ha]⟩)
  bounded := by
    intro v hv
    rcases hv with htop | hrest
    · exact le_of_eq (congrArg Prod.snd htop)
    · rcases hrest with himg | hfinal
      · obtain ⟨a, ha, rfl⟩ := himg
        exact (A.bounded a ha).trans (cut_le k n U b)
      · exact hUb v hfinal.1

/-- Adjoin the greatest vertex allowed by the time bound. -/
def addMax (k n : ℕ) (U : Set (Vertex k n)) (b : Fin (n + 1))
    (A : Chain k n U b) : Chain k n U b where
  toChain := {
    vertices := insert (Fin.last k, b) A.toChain.vertices
    chain := A.toChain.chain.insert (by
      intro v hv _
      exact Or.inr ⟨Fin.le_last _, A.bounded v hv⟩)
    covers := by
      intro i
      obtain ⟨j, hj⟩ := A.toChain.covers i
      exact ⟨j, Set.mem_insert_of_mem _ hj⟩ }
  contains := fun _ hv ↦ Set.mem_insert_of_mem _ (A.contains hv)
  bounded := by
    intro v hv
    rcases hv with htop | hv
    · exact le_of_eq (congrArg Prod.snd htop)
    · exact A.bounded v hv

/-- Every relative chain is included in its bounded maximum extension. -/
theorem le_addMax (k n : ℕ) (U : Set (Vertex k n)) (b : Fin (n + 1))
    (A : Chain k n U b) : A ≤ addMax k n U b A :=
  Set.subset_insert _ _

/-- Restriction of an extension recovers the earlier chain. -/
theorem restrict_extend (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b)
    (A : Chain k n (lower k n U) (cut k n U b)) :
    restrict k n U b (extend k n U b hU hUb A) = A := by
  cases A with
  | mk ac acov abound =>
    have hv : (restrict k n U b (extend k n U b hU hUb
        ⟨ac, acov, abound⟩)).toChain.vertices = ac.vertices := by
      ext v
      change lowerVertex k n v ∈ insert (Fin.last (k + 1), b)
        ((lowerVertex k n '' ac.vertices) ∪ final k n U) ↔ v ∈ ac.vertices
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_image]
      constructor
      · rintro (htop | (himg | hfinal))
        · exact False.elim (by
            have hc := congrArg Prod.fst htop
            exact (Fin.castSucc_ne_last v.1) hc)
        · obtain ⟨w, hw, hwv⟩ := himg
          exact (lowerVertex_injective k n hwv).symm ▸ hw
        · exact False.elim (by
            have hc := hfinal.2
            exact (Fin.castSucc_ne_last v.1) hc)
      · intro hv
        exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
    cases h : restrict k n U b (extend k n U b hU hUb
        ⟨ac, acov, abound⟩) with
    | mk rc rcov rbound =>
      simp only [h] at hv
      have hc : rc = ac := by
        cases rc with
        | mk rv rchain rcover =>
          cases ac with
          | mk av achain acover =>
            simp only at hv
            cases hv
            rfl
      cases hc
      rfl

/-- Extension after restriction lies in the bounded maximum extension. -/
theorem extend_restrict_le_addMax (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b)
    (A : Chain (k + 1) n U b) :
    extend k n U b hU hUb (restrict k n U b A) ≤ addMax (k + 1) n U b A := by
  intro v hv
  rcases hv with htop | hrest
  · exact Or.inl htop
  · rcases hrest with himg | hfinal
    · obtain ⟨w, hw, rfl⟩ := himg
      exact Or.inr hw
    · exact Or.inr (A.contains hfinal.1)

theorem addMax_monotone (k n : ℕ) (U : Set (Vertex k n))
    (b : Fin (n + 1)) : Monotone (addMax k n U b) := by
  intro A B h v hv
  rcases hv with htop | hA
  · exact Or.inl htop
  · exact Or.inr (h hA)

theorem restrict_monotone (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) : Monotone (restrict k n U b) := by
  intro A B h v hv
  exact h hv

theorem extend_monotone (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b) : Monotone (extend k n U b hU hUb) := by
  intro A B h v hv
  rcases hv with htop | hrest
  · exact Or.inl htop
  · rcases hrest with himg | hfinal
    · obtain ⟨w, hw, rfl⟩ := himg
      exact Or.inr (Or.inl ⟨w, h hw, rfl⟩)
    · exact Or.inr (Or.inr hfinal)

def restrictFunctor (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) :
    Chain (k + 1) n U b ⥤ Chain k n (lower k n U) (cut k n U b) :=
  (restrict_monotone k n U b).functor

def extendFunctor (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b) :
    Chain k n (lower k n U) (cut k n U b) ⥤ Chain (k + 1) n U b :=
  (extend_monotone k n U b hU hUb).functor

def addMaxFunctor (k n : ℕ) (U : Set (Vertex k n))
    (b : Fin (n + 1)) : Chain k n U b ⥤ Chain k n U b :=
  (addMax_monotone k n U b).functor

def idToAddMax (k n : ℕ) (U : Set (Vertex k n))
    (b : Fin (n + 1)) : 𝟭 (Chain k n U b) ⟶ addMaxFunctor k n U b where
  app A := homOfLE (le_addMax k n U b A)
  naturality _ _ _ := Subsingleton.elim _ _

def extendRestrictToAddMax (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b) :
    restrictFunctor k n U b ⋙ extendFunctor k n U b hU hUb ⟶
      addMaxFunctor (k + 1) n U b where
  app A := homOfLE (extend_restrict_le_addMax k n U b hU hUb A)
  naturality _ _ _ := Subsingleton.elim _ _

def extendRestrictToId (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b) :
    extendFunctor k n U b hU hUb ⋙ restrictFunctor k n U b ⟶
      𝟭 (Chain k n (lower k n U) (cut k n U b)) where
  app A := eqToHom (restrict_extend k n U b hU hUb A)
  naturality _ _ _ := Subsingleton.elim _ _

theorem restrict_geometricW (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b) :
    SSet.KanComplex.W (TopCat.toSSet.map
      (SSet.toTop.map (nerveMap (restrictFunctor k n U b)))) := by
  apply nerveMap_geometricW (restrictFunctor k n U b) (extendFunctor k n U b hU hUb)
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ ⟨extendRestrictToAddMax k n U b hU hUb⟩)
      (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ ⟨idToAddMax (k + 1) n U b⟩))
  · exact Relation.EqvGen.rel _ _ ⟨extendRestrictToId k n U b hU hUb⟩

theorem restrict_weak (k n : ℕ) (U : Set (Vertex (k + 1) n))
    (b : Fin (n + 1)) (hU : IsChain (· ≤ ·) U)
    (hUb : ∀ v ∈ U, v.2 ≤ b) :
    WeakEquivalence (nerveMap (restrictFunctor k n U b)) :=
  (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).mpr
    (restrict_geometricW k n U b hU hUb)

/-- The bounded full time line is the greatest one-coefficient chain. -/
def baseFull (n : ℕ) (U : Set (Vertex 0 n)) (b : Fin (n + 1))
    (hUb : ∀ v ∈ U, v.2 ≤ b) : Chain 0 n U b where
  toChain := {
    vertices := {v | v.2 ≤ b}
    chain := by
      intro a _ c _ _
      rcases a with ⟨i, j⟩
      rcases c with ⟨i', j'⟩
      have hi : i = i' := by rw [Fin.eq_zero i, Fin.eq_zero i']
      subst i'
      rcases le_total j j' with h | h
      · exact Or.inl ⟨le_rfl, h⟩
      · exact Or.inr ⟨le_rfl, h⟩
    covers := by
      intro i
      exact ⟨0, Fin.zero_le b⟩ }
  contains := fun v hv ↦ hUb v hv
  bounded := fun v hv ↦ hv

private theorem le_baseFull (n : ℕ) (U : Set (Vertex 0 n))
    (b : Fin (n + 1)) (hUb : ∀ v ∈ U, v.2 ≤ b)
    (A : Chain 0 n U b) : A ≤ baseFull n U b hUb := by
  intro v hv
  exact A.bounded v hv

/-- Relative full-support chains at one coefficient level have a terminal object. -/
def baseTerminal (n : ℕ) (U : Set (Vertex 0 n))
    (b : Fin (n + 1)) (hUb : ∀ v ∈ U, v.2 ≤ b) :
    IsTerminal (baseFull n U b hUb) :=
  IsTerminal.ofUniqueHom (fun A ↦ homOfLE (le_baseFull n U b hUb A))
    (fun _ _ ↦ Subsingleton.elim _ _)

private theorem base_point_GW (n : ℕ) (U : Set (Vertex 0 n))
    (b : Fin (n + 1)) (hUb : ∀ v ∈ U, v.2 ≤ b) :
    GW (pointMap (nerve (Chain 0 n U b))) := by
  let E := Chain 0 n U b
  let e : E := baseFull n U b hUb
  let he : IsTerminal e := baseTerminal n U b hUb
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

private theorem point_GW_by_levels (n : ℕ) :
    ∀ (k : ℕ) (U : Set (Vertex k n)) (b : Fin (n + 1)),
      IsChain (· ≤ ·) U → (∀ v ∈ U, v.2 ≤ b) →
        GW (pointMap (nerve (Chain k n U b))) := by
  intro k
  induction k with
  | zero =>
    intro U b _ hUb
    exact base_point_GW n U b hUb
  | succ k ih =>
    intro U b hU hUb
    have hlowerchain : IsChain (· ≤ ·) (lower k n U) :=
      IsChain.preimage (· ≤ ·) (· ≤ ·) (lowerVertex k n)
        (lowerVertex_injective k n)
        (by intro a c h; exact (lowerVertex_le_iff k n a c).mp h) hU
    have hlowerbound : ∀ v ∈ lower k n U, v.2 ≤ cut k n U b := by
      intro v hv
      exact lower_bounded k n U b hU hUb hv
    have hlow : GW (pointMap (nerve (Chain k n (lower k n U) (cut k n U b)))) :=
      ih (lower k n U) (cut k n U b) hlowerchain hlowerbound
    have hr : WeakEquivalence (nerveMap (restrictFunctor k n U b)) :=
      restrict_weak k n U b hU hUb
    have hl : WeakEquivalence
        (pointMap (nerve (Chain k n (lower k n U) (cut k n U b)))) :=
      (weakEquivalence_iff_GW _).mpr hlow
    have hm : nerveMap (restrictFunctor k n U b) ≫
        pointMap (nerve (Chain k n (lower k n U) (cut k n U b))) =
        pointMap (nerve (Chain (k + 1) n U b)) :=
      pointIsTerminal.hom_ext _ _
    apply (weakEquivalence_iff_GW _).mp
    rw [← hm]
    infer_instance

/-- Weak contractibility of bounded full-support chains containing a partial chain. -/
theorem point_GW (k n : ℕ) (U : Set (Vertex k n)) (b : Fin (n + 1))
    (hU : IsChain (· ≤ ·) U) (hUb : ∀ v ∈ U, v.2 ≤ b) :
    GW (pointMap (nerve (Chain k n U b))) :=
  point_GW_by_levels n k U b hU hUb

end
end DaggerModels.PartII.TimePrismChainRelative
