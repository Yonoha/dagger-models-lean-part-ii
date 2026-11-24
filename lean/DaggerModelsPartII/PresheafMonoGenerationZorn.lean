import DaggerModelsPartII.PresheafMonoGenerationChains
import Mathlib.Order.Zorn

set_option autoImplicit false
open CategoryTheory Limits
universe u v
namespace DaggerModels.PartII.PresheafMonoGeneration
variable {D : Type u} [Category.{u} D]

/-- A compatible lift of a map over a subfunctor, extending an initial partial lift. -/
structure PartialLift {B X Y : D ⥤ Type v} (p : X ⟶ Y) (β : B ⟶ Y)
    (S₀ : Subfunctor B) (s₀ : S₀.toFunctor ⟶ X) where
  S : Subfunctor B
  contains : S₀ ≤ S
  lift : S.toFunctor ⟶ X
  agrees : Subfunctor.homOfLe contains ≫ lift = s₀
  over : lift ≫ p = S.ι ≫ β

namespace PartialLift
variable {B X Y : D ⥤ Type v} {p : X ⟶ Y} {β : B ⟶ Y}
  {S₀ : Subfunctor B} {s₀ : S₀.toFunctor ⟶ X}

instance : LE (PartialLift p β S₀ s₀) where
  le P Q := ∃ h : P.S ≤ Q.S, Subfunctor.homOfLe h ≫ Q.lift = P.lift

instance : Preorder (PartialLift p β S₀ s₀) where
  le_refl P := ⟨le_refl P.S, by ext d z; rfl⟩
  le_trans P Q R hPQ hQR := by
    obtain ⟨hPQ, ePQ⟩ := hPQ
    obtain ⟨hQR, eQR⟩ := hQR
    refine ⟨hPQ.trans hQR, ?_⟩
    ext d z
    have h := congrArg (fun α => α.app d z) ePQ
    have h' := congrArg (fun α => α.app d
      ((Subfunctor.homOfLe hPQ).app d z)) eQR
    exact h'.trans h


/-- Every nonempty chain of compatible partial lifts has a union lift. -/
theorem chain_bddAbove
    (c : Set (PartialLift p β S₀ s₀))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) : BddAbove c := by
  let I := { P : PartialLift p β S₀ s₀ // P ∈ c }
  let SS : I → Subfunctor B := fun P => P.1.S
  let tt : ∀ P : I, (SS P).toFunctor ⟶ X := fun P => P.1.lift
  have compat : ∀ i j d (y : B.obj d) (hi : y ∈ (SS i).obj d)
      (hj : y ∈ (SS j).obj d),
      (tt i).app d ⟨y, hi⟩ = (tt j).app d ⟨y, hj⟩ := by
    intro i j d y hi hj
    rcases hc.total i.2 j.2 with h | h
    · obtain ⟨hS, ht⟩ := h
      have he := congrArg (fun α => α.app d ⟨y, hi⟩) ht
      simpa [SS, tt, Subfunctor.homOfLe] using he.symm
    · obtain ⟨hS, ht⟩ := h
      have he := congrArg (fun α => α.app d ⟨y, hj⟩) ht
      simpa [SS, tt, Subfunctor.homOfLe] using he
  let T : Subfunctor B := ⨆ i : I, SS i
  let t : T.toFunctor ⟶ X := glueOnISup SS tt compat
  obtain ⟨P₀, hP₀⟩ := hne
  let i₀ : I := ⟨P₀, hP₀⟩
  have hcontains : S₀ ≤ T := P₀.contains.trans (le_iSup SS i₀)
  have hagrees : Subfunctor.homOfLe hcontains ≫ t = s₀ := by
    ext d z
    have hres := congrArg (fun α => α.app d
      ((Subfunctor.homOfLe P₀.contains).app d z))
      (homOfLe_glueOnISup SS tt compat i₀)
    have hinit := congrArg (fun α => α.app d z) P₀.agrees
    exact hres.trans hinit
  have hover : t ≫ p = T.ι ≫ β := by
    ext d z
    obtain ⟨i, hi⟩ : ∃ i : I, z.val ∈ (SS i).obj d := by
      simpa [T, Subfunctor.iSup_obj] using z.property
    have hres := congrArg (fun α => α.app d ⟨z.val, hi⟩)
      (homOfLe_glueOnISup SS tt compat i)
    have hpart := congrArg (fun α => α.app d ⟨z.val, hi⟩) i.1.over
    simpa [NatTrans.comp_app, Subfunctor.homOfLe, Subfunctor.ι] using
      (congrArg (p.app d) hres).trans hpart
  let P : PartialLift p β S₀ s₀ := ⟨T, hcontains, t, hagrees, hover⟩
  refine ⟨P, ?_⟩
  intro Q hQ
  let i : I := ⟨Q, hQ⟩
  exact ⟨le_iSup SS i, homOfLe_glueOnISup SS tt compat i⟩


/-- If every cyclic intersection inclusion lifts, every partial lift extends to
all of the ambient Type-valued functor. -/
theorem extendLiftToWhole (h₀ : s₀ ≫ p = S₀.ι ≫ β)
    (hcyclic : ∀ (S : Subfunctor B) (d : D) (x : B.obj d),
      HasLiftingProperty
        (Subfunctor.homOfLe
          (inf_le_right : S ⊓ cyclicSubfunctor B x ≤ cyclicSubfunctor B x)) p) :
    ∃ t : B ⟶ X, S₀.ι ≫ t = s₀ ∧ t ≫ p = β := by
  let P₀ : PartialLift p β S₀ s₀ :=
    ⟨S₀, le_refl S₀, s₀, by ext d z; rfl, h₀⟩
  letI : Nonempty (PartialLift p β S₀ s₀) := ⟨P₀⟩
  obtain ⟨M, hmax⟩ := zorn_le_nonempty
    (fun c hc hne => chain_bddAbove (p := p) (β := β) (S₀ := S₀) (s₀ := s₀) c hc hne)
  have htop : M.S = ⊤ := by
    by_contra hne
    have hex : ∃ d : D, ∃ x : B.obj d, x ∉ M.S.obj d := by
      by_contra h
      push_neg at h
      apply hne
      ext d x
      constructor
      · intro _; trivial
      · intro _; exact h d x
    obtain ⟨d, x, hx⟩ := hex
    let T := cyclicSubfunctor B x
    obtain ⟨u, hu, hover⟩ :=
      extendLiftAcrossUnion M.S T p β M.lift M.over (hcyclic M.S d x)
    let P : PartialLift p β S₀ s₀ := {
      S := M.S ⊔ T
      contains := M.contains.trans le_sup_left
      lift := u
      agrees := by
        calc
          Subfunctor.homOfLe (M.contains.trans le_sup_left) ≫ u =
              (Subfunctor.homOfLe M.contains ≫
                Subfunctor.homOfLe le_sup_left) ≫ u := by ext d z; rfl
          _ = Subfunctor.homOfLe M.contains ≫ M.lift := by rw [Category.assoc, hu]
          _ = s₀ := M.agrees
      over := hover }
    have hmP : M ≤ P := ⟨le_sup_left, hu⟩
    have hPM : P ≤ M := hmax hmP
    have hxM : x ∈ M.S.obj d :=
      hPM.1 d ((le_sup_right : T ≤ M.S ⊔ T) d (mem_cyclicSubfunctor B x))
    exact hx hxM
  haveI : IsIso M.S.ι := (Subfunctor.eq_top_iff_isIso M.S).mp htop
  let t : B ⟶ X := inv M.S.ι ≫ M.lift
  refine ⟨t, ?_, ?_⟩
  · calc
      S₀.ι ≫ t = (Subfunctor.homOfLe M.contains ≫ M.S.ι) ≫
          (inv M.S.ι ≫ M.lift) := by rw [Subfunctor.homOfLe_ι]
      _ = Subfunctor.homOfLe M.contains ≫ M.lift := by
        have he : (Subfunctor.homOfLe M.contains ≫ M.S.ι) ≫
            inv M.S.ι = Subfunctor.homOfLe M.contains := by
          rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        simp only [← Category.assoc, he]
      _ = s₀ := M.agrees
  · apply (cancel_epi M.S.ι).mp
    calc
      M.S.ι ≫ (t ≫ p) = M.lift ≫ p := by simp [t]
      _ = M.S.ι ≫ β := M.over


/-- The cyclic-intersection lifting condition implies lifting against every
monomorphism of Type-valued functors. -/
theorem mono_hasLiftingProperty_of_cyclic {A B X Y : D ⥤ Type v}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y)
    (hcyclic : ∀ (S : Subfunctor B) (d : D) (x : B.obj d),
      HasLiftingProperty
        (Subfunctor.homOfLe
          (inf_le_right : S ⊓ cyclicSubfunctor B x ≤ cyclicSubfunctor B x)) p) :
    HasLiftingProperty i p := by
  refine ⟨fun {a} {β} sq => ?_⟩
  let S₀ := Subfunctor.range i
  haveI : IsIso (Subfunctor.toRange i) := inferInstance
  let s₀ : S₀.toFunctor ⟶ X := inv (Subfunctor.toRange i) ≫ a
  have h₀ : s₀ ≫ p = S₀.ι ≫ β := by
    apply (cancel_epi (Subfunctor.toRange i)).mp
    calc
      Subfunctor.toRange i ≫ (s₀ ≫ p) = a ≫ p := by simp [s₀]
      _ = i ≫ β := sq.w
      _ = Subfunctor.toRange i ≫ (S₀.ι ≫ β) := by simp [S₀]
  obtain ⟨t, ht₁, ht₂⟩ :=
    extendLiftToWhole (p := p) (β := β) (S₀ := S₀) (s₀ := s₀) h₀ hcyclic
  refine CommSq.HasLift.mk' ⟨t, ?_, ht₂⟩
  calc
    i ≫ t = (Subfunctor.toRange i ≫ S₀.ι) ≫ t := by simp [S₀]
    _ = Subfunctor.toRange i ≫ s₀ := by rw [Category.assoc, ht₁]
    _ = a := by simp [s₀]

end PartialLift
end DaggerModels.PartII.PresheafMonoGeneration
