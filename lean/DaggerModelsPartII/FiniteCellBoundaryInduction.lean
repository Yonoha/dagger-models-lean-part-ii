import TopCatModelCategory.SSet.FiniteInduction
import TopCatModelCategory.SSet.Boundary
import TopCatModelCategory.SSet.NonDegenerateSimplices

/-!
# Finite simplicial-set induction with a boundary premise

The helper `topCellPushout` removes a chosen top-dimensional nondegenerate
simplex and retains its dimension in the boundary attachment. The main theorem
uses dimension induction and a finite nondegenerate-cell induction; its
boundary premise is supplied at each step by the smaller dimension, without
assuming a global boundary property.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Limits Opposite

namespace DaggerModels.PartII.FiniteCellBoundaryInduction

noncomputable section

/-- Remove one top-dimensional nondegenerate simplex and attach it along its
literal boundary. The construction is copied from the proof of
`SSet.finite_induction`, keeping the selected dimension `n` in the output. -/
private theorem topCellPushout {X : SSet.{0}} [X.IsFinite] (n : ℕ)
    (hdim : X.HasDimensionLT (n + 1)) (hnot : ¬ X.HasDimensionLT n) :
    ∃ (A : X.Subcomplex) (_ : A ≠ ⊤)
      (t : (SSet.boundary n : SSet.{0}) ⟶ (A : SSet.{0}))
      (b : Δ[n] ⟶ X), IsPushout t (SSet.boundary n).ι A.ι b := by
  letI : X.HasDimensionLT (n + 1) := hdim
  obtain ⟨x, hx⟩ : Nonempty (X.nonDegenerate n) := by
    by_contra!
    apply hnot
    constructor
    intro d hd
    obtain hd | rfl := hd.lt_or_eq
    · apply X.degenerate_eq_top_of_hasDimensionLT (n + 1) d (by omega)
    · ext y
      simp at this ⊢
      rw [SSet.mem_degenerate_iff_notMem_nonDegenerate, this]
      simp
  let A : X.Subcomplex := ⨆ (s : ({SSet.N.mk x hx}ᶜ : Set X.N)), s.1.subcomplex
  have hxA : x ∉ A.obj _ := fun hxA ↦ by
    simp only [A, Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_iUnion, exists_prop] at hxA
    obtain ⟨s, hs, hx'⟩ := hxA
    have hs' : SSet.N.mk x hx < s := by
      refine lt_of_le_of_ne ?_ (Ne.symm hs)
      rwa [SSet.N.le_iff, Subfunctor.ofSection_le_iff]
    have hlt := SSet.N.lt_of_lt hs'
    dsimp at hlt
    have hdimS := X.dim_lt_of_nondegenerate ⟨_, s.nonDegenerate⟩ (n + 1)
    omega
  have hA : A ≠ ⊤ := fun heq ↦ by simp [heq] at hxA
  have hLow {d : ℕ} (hd : d < n) (y : X.obj (op ⦋d⦌)) : y ∈ A.obj _ := by
    obtain ⟨e, f, _, ⟨z, hz⟩, hzy⟩ := X.exists_nonDegenerate y
    have he : e ≤ d := SimplexCategory.len_le_of_epi f
    have hne : SSet.N.mk z hz ≠ SSet.N.mk x hx := by
      intro h
      have hed : e = n := by
        rw [SSet.N.ext_iff] at h
        exact SSet.S.dim_eq_of_eq h
      omega
    have hzA : z ∈ A.obj _ := by
      simp only [A, Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
        Set.mem_singleton_iff, Set.mem_iUnion, exists_prop]
      exact ⟨SSet.N.mk z hz, hne, SSet.Subcomplex.mem_ofSimplex_obj z⟩
    rw [hzy]
    exact A.map f.op hzA
  let A' := A ⊔ SSet.Subcomplex.ofSimplex x
  have hA' : x ∈ A'.obj _ := Or.inr (SSet.Subcomplex.mem_ofSimplex_obj x)
  have htop : A' = ⊤ := by
    rw [SSet.Subcomplex.eq_top_iff_contains_nonDegenerate]
    intro d y hy
    by_cases hxy : SSet.N.mk y hy = SSet.N.mk x hx
    · obtain rfl : d = n := by
        rw [SSet.N.ext_iff] at hxy
        exact SSet.S.dim_eq_of_eq hxy
      obtain rfl : y = x := by
        simpa [SSet.N.ext_iff, SSet.S.ext_iff'] using hxy
      exact Or.inr (SSet.Subcomplex.mem_ofSimplex_obj y)
    · apply Or.inl
      simp only [Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
        Set.mem_singleton_iff, Set.mem_iUnion, exists_prop, A]
      exact ⟨SSet.N.mk y hy, hxy, SSet.Subcomplex.mem_ofSimplex_obj y⟩
  have hpre : A.preimage (SSet.yonedaEquiv.symm x) = SSet.boundary n := by
    rw [SSet.stdSimplex.eq_boundary_iff]
    constructor
    · rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
      intro d ⟨y, hy⟩ hy'
      change (SSet.yonedaEquiv.symm x).app (op ⦋d⦌) y ∈ A.obj _
      exact hLow (SSet.dim_lt_of_nondegenerate (X := SSet.boundary n)
        ⟨⟨y, hy'⟩, (SSet.Subcomplex.mem_nonDegenerate_iff _ ⟨y, hy'⟩).2 hy⟩ n) _
    · intro h
      apply hxA
      simpa using h.symm.le _ (by simp : SSet.yonedaEquiv (𝟙 _) ∈ _)
  let t : (SSet.boundary n : SSet.{0}) ⟶ (A : SSet.{0}) :=
    SSet.Subcomplex.liftFromPreimage
      ((SSet.boundary n).ι ≫ SSet.yonedaEquiv.symm x) (by
        rw [SSet.Subcomplex.preimage_eq_top_iff,
          SSet.Subcomplex.range_le_iff_nonDegenerate]
        intro d y
        exact hLow (SSet.dim_lt_of_nondegenerate _ y n) _)
  let b : Δ[n] ⟶ (A' : SSet.{0}) := SSet.yonedaEquiv.symm ⟨x, hA'⟩
  have sq : IsPushout t (SSet.boundary n).ι
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A')) b := by
    refine ⟨⟨rfl⟩, ⟨evaluationJointlyReflectsColimits _ (fun ⟨m⟩ ↦
      (PushoutCocone.isColimitMapCoconeEquiv _ _).2 ?_)⟩⟩
    apply IsPushout.isColimit
    dsimp
    refine Types.isPushout_of_isPullback_of_mono (X₅ := X.obj _) (k := Subtype.val)
      (r' := Subtype.val) (b' := (SSet.yonedaEquiv.symm x).app _) ?_ rfl rfl
        (le_antisymm (by simp) ?_) ?_
    · exact Types.isPullback_of_eq_setPreimage (f := (SSet.yonedaEquiv.symm x).app _) _
        (by simp [← hpre])
    · rintro ⟨y, hy⟩ _
      simp only [Set.mem_union] at hy
      simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Subtype.exists]
      obtain hy | ⟨z, hz⟩ := hy
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ⟨SSet.stdSimplex.objEquiv.symm z.unop,
          by rwa [Subtype.ext_iff]⟩
    · induction m using SimplexCategory.rec with | _ m
      intro x₃ y₃ hx₃ hy₃ h
      simp only [Set.mem_range, Subfunctor.ι_app, Subtype.exists,
        exists_prop, exists_eq_right] at hx₃ hy₃
      obtain ⟨φ, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective x₃
      obtain ⟨ψ, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective y₃
      dsimp at φ ψ
      have : Epi φ := by
        rw [SimplexCategory.epi_iff_surjective]
        exact not_not.1 hx₃
      have : Epi ψ := by
        rw [SimplexCategory.epi_iff_surjective]
        exact not_not.1 hy₃
      obtain rfl := X.unique_nonDegenerate_map _ φ ⟨x, hx⟩ rfl ψ ⟨x, hx⟩ h
      rfl
  let e : (A' : SSet.{0}) ≅ X :=
    SSet.Subcomplex.isoOfEq htop ≪≫ SSet.Subcomplex.topIso X
  have he : e.hom = A'.ι := by
    change SSet.Subcomplex.homOfLE (by rw [htop]) ≫ (⊤ : X.Subcomplex).ι = A'.ι
    exact SSet.Subcomplex.homOfLE_ι _
  refine ⟨A, hA, t, b ≫ e.hom, sq.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e rfl rfl ?_ rfl⟩
  rw [he]
  exact SSet.Subcomplex.homOfLE_ι _

/-- Boundary-sensitive finite induction. The top-cell dimension is retained,
so the boundary premise is supplied by the outer dimension induction; the
proper subcomplex premise is supplied by inner nondegenerate-cell induction. -/
theorem finite_induction_with_boundary (P : SSet.{0} → Prop)
    (hEmpty : ∀ (X : SSet.{0}) [X.HasDimensionLT 0], P X)
    (hSimplex : ∀ n : ℕ, P Δ[n])
    (hAttach : ∀ ⦃A X : SSet.{0}⦄ (i : A ⟶ X) ⦃n : ℕ⦄
      ⦃t : (SSet.boundary n : SSet.{0}) ⟶ A⦄ ⦃b : Δ[n] ⟶ X⦄,
      IsPushout t (SSet.boundary n).ι i b →
      P A → P (SSet.boundary n : SSet.{0}) → P Δ[n] → P X)
    (X : SSet.{0}) [X.IsFinite] : P X := by
  have hAll : ∀ d : ℕ, ∀ (Y : SSet.{0}) [Y.IsFinite], Y.HasDimensionLT d → P Y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d hDim =>
      intro Y _ hY
      have hCells : ∀ c : ℕ, ∀ (Z : SSet.{0}) [Z.IsFinite],
          Nat.card Z.N = c → Z.HasDimensionLT d → P Z := by
        intro c
        induction c using Nat.strong_induction_on with
        | _ c hCell =>
          intro Z _ hc hZ
          obtain _ | n := d
          · letI : Z.HasDimensionLT 0 := hZ
            exact hEmpty Z
          · by_cases hLow : Z.HasDimensionLT n
            · exact hDim n (by omega) Z hLow
            · obtain ⟨A, hA, t, b, sq⟩ := topCellPushout n hZ hLow
              have hCard : Nat.card A.toSSet.N < c := by
                simpa [← hc] using A.natCard_n_lt_of_ne_top hA
              have hPA : P (A : SSet.{0}) :=
                hCell _ hCard A rfl (by infer_instance)
              have hBoundary : P (SSet.boundary n : SSet.{0}) :=
                hDim n (by omega) _ (by infer_instance)
              exact hAttach A.ι sq hPA hBoundary (hSimplex n)
      exact hCells (Nat.card Y.N) Y rfl hY
  obtain ⟨d, hdim⟩ := X.hasDimensionLT_of_isFinite
  exact hAll d X hdim

end

end DaggerModels.PartII.FiniteCellBoundaryInduction
