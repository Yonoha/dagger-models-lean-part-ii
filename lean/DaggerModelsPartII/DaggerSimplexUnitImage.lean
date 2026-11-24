import DaggerModelsPartII.DaggerSimplexNerveNaturality

/-!
# The image of the reversal-simplex change of index

A dagger functor between free dagger simplices lies in the image of `u`
precisely when its positive adjacent generators are sent uniformly to
forward interval words or uniformly to daggered backward interval words.
Identity words are included when adjacent vertices have equal images.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexPartIIndex

namespace DaggerModels.PartII.DaggerSimplexUnitImage

noncomputable section

/-- The vertex function underlying a dagger functor of free simplices. -/
def vertexMap {m n : ℕ}
    (F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩)
    (i : Fin (m + 1)) : Fin (n + 1) :=
  ⟨(F.toFunctor.obj (⟨⟨i.val, i.isLt⟩⟩ : FreeDaggerSimplex m)).vertex.val,
    (F.toFunctor.obj (⟨⟨i.val, i.isLt⟩⟩ : FreeDaggerSimplex m)).vertex.isLt⟩

/-- Every positive generator maps to exactly the forward word between the
images of its endpoints. The inequality is part of the word data. -/
def ForwardWordImages {m n : ℕ}
    (F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩) : Prop :=
  ∀ a : Fin m, ∃ h : vertexMap F a.castSucc ≤ vertexMap F a.succ,
    F.toFunctor.map (forwardEdge m a.val (Nat.succ_le_of_lt a.isLt)) =
      forwardWord n (vertexMap F a.castSucc).val (vertexMap F a.succ).val
        (Nat.lt_succ_iff.mp (vertexMap F a.castSucc).isLt)
        (Nat.lt_succ_iff.mp (vertexMap F a.succ).isLt) h

/-- Every positive generator maps to exactly the dagger of the forward
word in the opposite direction. Empty words include constant maps. -/
def BackwardWordImages {m n : ℕ}
    (F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩) : Prop :=
  ∀ a : Fin m, ∃ h : vertexMap F a.succ ≤ vertexMap F a.castSucc,
    F.toFunctor.map (forwardEdge m a.val (Nat.succ_le_of_lt a.isLt)) =
      dagger (forwardWord n (vertexMap F a.succ).val (vertexMap F a.castSucc).val
        (Nat.lt_succ_iff.mp (vertexMap F a.succ).isLt)
        (Nat.lt_succ_iff.mp (vertexMap F a.castSucc).isLt) h)

/-- The source of the image criterion is an actual reversal map. -/
def InImage {m n : ℕ}
    (F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩) : Prop :=
  ∃ α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n), u.map α = F

@[simp] theorem vertexMap_u {m n : ℕ}
    (α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n))
    (i : Fin (m + 1)) : vertexMap (u.map α) i = α.toFun i := rfl

theorem forwardWordImages_u {m n : ℕ}
    (α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n))
    (hα : Monotone α.toFun) : ForwardWordImages (u.map α) := by
  intro a
  refine ⟨hα (Fin.castSucc_le_succ a), ?_⟩
  simpa only [vertexMap_u] using
    u_map_generator_monotone α hα a.val (Nat.succ_le_of_lt a.isLt)

theorem backwardWordImages_u {m n : ℕ}
    (α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n))
    (hα : Antitone α.toFun) : BackwardWordImages (u.map α) := by
  intro a
  refine ⟨hα (Fin.castSucc_le_succ a), ?_⟩
  simpa only [vertexMap_u] using
    u_map_generator_antitone α hα a.val (Nat.succ_le_of_lt a.isLt)

theorem monotone_vertexMap_of_forward {m n : ℕ}
    {F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩}
    (h : ForwardWordImages F) : Monotone (vertexMap F) :=
  Fin.monotone_iff_le_succ.mpr (fun a ↦ (h a).choose)

theorem antitone_vertexMap_of_backward {m n : ℕ}
    {F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩}
    (h : BackwardWordImages F) : Antitone (vertexMap F) :=
  Fin.antitone_iff_succ_le.mpr (fun a ↦ (h a).choose)

theorem inImage_of_forward {m n : ℕ}
    {F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩}
    (h : ForwardWordImages F) : InImage F := by
  let α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n) :=
    ⟨vertexMap F, Or.inl (monotone_vertexMap_of_forward h)⟩
  refine ⟨α, ?_⟩
  apply DaggerSimplex.Hom.ext
  have hr :
      DaggerSimplexFreeProperty.restrict m (FreeDaggerSimplex n)
        ⟨(u.map α).toFunctor, (u.map α).map_dagger⟩ =
      DaggerSimplexFreeProperty.restrict m (FreeDaggerSimplex n)
        ⟨F.toFunctor, F.map_dagger⟩ := by
    change DaggerSimplexFreeProperty.ChainData.mk _ _ =
      DaggerSimplexFreeProperty.ChainData.mk _ _
    congr 1
    funext a b e
    have hab : a.val + 1 = b.val := e.down
    cases a with
    | mk av ah =>
      cases b with
      | mk bv bh =>
        dsimp at hab
        subst bv
        let aa : Fin m := ⟨av, by omega⟩
        obtain ⟨hmono, hword⟩ := h aa
        change PLift (av + 1 = av + 1) at e
        rcases e with ⟨e⟩
        change (u.map α).toFunctor.map (forwardEdge m av (by omega)) =
          F.toFunctor.map (forwardEdge m av (by omega))
        rw [u_map_generator_monotone α (monotone_vertexMap_of_forward h)]
        simpa [α, aa, vertexMap] using hword.symm
  have heq :=
    (DaggerSimplexFreeProperty.freeDaggerSimplexHomEquiv m
      (FreeDaggerSimplex n)).symm.injective hr
  exact congrArg Subtype.val heq

theorem inImage_of_backward {m n : ℕ}
    {F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩}
    (h : BackwardWordImages F) : InImage F := by
  let α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n) :=
    ⟨vertexMap F, Or.inr (antitone_vertexMap_of_backward h)⟩
  refine ⟨α, ?_⟩
  apply DaggerSimplex.Hom.ext
  have hr :
      DaggerSimplexFreeProperty.restrict m (FreeDaggerSimplex n)
        ⟨(u.map α).toFunctor, (u.map α).map_dagger⟩ =
      DaggerSimplexFreeProperty.restrict m (FreeDaggerSimplex n)
        ⟨F.toFunctor, F.map_dagger⟩ := by
    change DaggerSimplexFreeProperty.ChainData.mk _ _ =
      DaggerSimplexFreeProperty.ChainData.mk _ _
    congr 1
    funext a b e
    have hab : a.val + 1 = b.val := e.down
    cases a with
    | mk av ah =>
      cases b with
      | mk bv bh =>
        dsimp at hab
        subst bv
        let aa : Fin m := ⟨av, by omega⟩
        obtain ⟨hanti, hword⟩ := h aa
        change PLift (av + 1 = av + 1) at e
        rcases e with ⟨e⟩
        change (u.map α).toFunctor.map (forwardEdge m av (by omega)) =
          F.toFunctor.map (forwardEdge m av (by omega))
        rw [u_map_generator_antitone α (antitone_vertexMap_of_backward h)]
        simpa [α, aa, vertexMap] using hword.symm
  have heq :=
    (DaggerSimplexFreeProperty.freeDaggerSimplexHomEquiv m
      (FreeDaggerSimplex n)).symm.injective hr
  exact congrArg Subtype.val heq

/-- A genuine uniform word criterion for the image of the change-of-index
functor. No cancellation of a word with its dagger is used. -/
theorem inImage_iff_wordImages {m n : ℕ}
    (F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩) :
    InImage F ↔ ForwardWordImages F ∨ BackwardWordImages F := by
  constructor
  · rintro ⟨α, rfl⟩
    rcases α.monotone_or_antitone with hα | hα
    · exact Or.inl (forwardWordImages_u α hα)
    · exact Or.inr (backwardWordImages_u α hα)
  · rintro (h | h)
    · exact inImage_of_forward h
    · exact inImage_of_backward h

/-- Image membership for the exact Part I free enriched dagger simplices. -/
def ActualInImage {m n : ℕ}
    (F : (⟨m⟩ : ActualDaggerSimplex) ⟶ ⟨n⟩) : Prop :=
  ∃ α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n), actualU.map α = F

/-- The same word criterion for all enriched dagger functors between the
actual Part I free objects, using the canonical comparison isomorphisms. -/
theorem actualInImage_iff_wordImages {m n : ℕ}
    (F : (⟨m⟩ : ActualDaggerSimplex) ⟶ ⟨n⟩) :
    ActualInImage F ↔
      ForwardWordImages ((actualHomEquiv ⟨m⟩ ⟨n⟩).symm F) ∨
      BackwardWordImages ((actualHomEquiv ⟨m⟩ ⟨n⟩).symm F) := by
  rw [← inImage_iff_wordImages]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, ?_⟩
    apply (actualHomEquiv ⟨m⟩ ⟨n⟩).injective
    simpa only [Equiv.apply_symm_apply] using hα
  · rintro ⟨α, hα⟩
    refine ⟨α, ?_⟩
    change (actualHomEquiv ⟨m⟩ ⟨n⟩) (u.map α) = F
    rw [hα]
    simp

/-- In degree zero there are no positive generators, so every dagger
functor is in the image; both uniform word conditions hold vacuously. -/
theorem zero_forward_and_backward (n : ℕ)
    (F : (⟨0⟩ : DaggerSimplex) ⟶ ⟨n⟩) :
    ForwardWordImages F ∧ BackwardWordImages F := by
  constructor <;> intro a <;> exact Fin.elim0 a

theorem zero_inImage (n : ℕ)
    (F : (⟨0⟩ : DaggerSimplex) ⟶ ⟨n⟩) : InImage F :=
  inImage_of_forward (zero_forward_and_backward n F).1

/-- Constant reversal maps satisfy both orientations. Collapsed adjacent
generators are sent to identity words by the included word formulas. -/
theorem constantMap_forward_and_backward {m n : ℕ}
    (α : (ReverseSimplex.mk m) ⟶ (ReverseSimplex.mk n))
    (hconst : ∀ i j, α.toFun i = α.toFun j) :
    ForwardWordImages (u.map α) ∧ BackwardWordImages (u.map α) := by
  have h := (ReverseSimplex.monotone_antitone_iff_constant α.toFun).2 hconst
  exact ⟨forwardWordImages_u α h.1, backwardWordImages_u α h.2⟩

end

end DaggerModels.PartII.DaggerSimplexUnitImage
