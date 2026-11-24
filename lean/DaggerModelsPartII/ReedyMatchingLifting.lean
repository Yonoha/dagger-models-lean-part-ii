import DaggerModelsPartII.ReedyMaps
import DaggerModelsPartII.RankedConeLifting
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! Lifting against the map of matching objects using lower relative matching maps. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Opposite Simplicial

universe v u

namespace DaggerModels.PartII

private def matchingIndexOfArrow {n : ℕ} {s : SimplexCategoryᵒᵖ}
    (a : op ⦋n⦌ ⟶ s) (hs : s.unop.len < n) (ha : Mono a.unop) : MatchingIndex n :=
  ⟨StructuredArrow.mk a, hs, ha⟩

private theorem matchingIndex_eq_of_right {n : ℕ} {s t : MatchingIndex n}
    (h : s.obj.right = t.obj.right) (w : s.obj.hom ≫ eqToHom h = t.obj.hom) : s = t :=
  ObjectProperty.FullSubcategory.ext (StructuredArrow.obj_ext _ _ h w)

private theorem simplexOp_eqToHom_of_unop_mono {s t : SimplexCategoryᵒᵖ}
    (a : s ⟶ t) (h : s = t) [Mono a.unop] : a = eqToHom h := by
  subst t
  apply Quiver.Hom.unop_inj
  exact SimplexCategory.eq_id_of_mono a.unop

private def matchingDegree {n : ℕ} (s : MatchingIndex n) : ℕ :=
  s.obj.right.unop.len

private theorem matchingIndex_decreases {n : ℕ} {s t : MatchingIndex n} (f : s ⟶ t) :
    t.obj.right.unop.len < s.obj.right.unop.len ∨ ∃ h : s = t, f = eqToHom h := by
  letI := matchingIndex_map_mono f
  rcases lt_or_eq_of_le (SimplexCategory.len_le_of_mono f.hom.right.unop) with h | h
  · exact Or.inl h
  · have hr : s.obj.right = t.obj.right :=
      congrArg Opposite.op (SimplexCategory.ext _ _ h.symm)
    have hf := simplexOp_eqToHom_of_unop_mono f.hom.right hr
    have he := matchingIndex_eq_of_right hr (hf ▸ StructuredArrow.w f.hom)
    right
    refine ⟨he, ObjectProperty.hom_ext _ (StructuredArrow.hom_ext _ _ ?_)⟩
    rw [hf]
    subst t
    rfl

/-- Compose a proper face of `[k]` with a face `[k] → [n]`. -/
private def matchingCompose {n k : ℕ} (a : op ⦋n⦌ ⟶ op ⦋k⦌)
    (hk : k < n) [Mono a.unop] : MatchingIndex k ⥤ MatchingIndex n :=
  ObjectProperty.lift _ ((matchingIndexProperty k).ι ⋙ StructuredArrow.map a) (fun s ↦ by
    refine ⟨lt_trans s.property.1 hk, ?_⟩
    letI := s.property.2
    change Mono (s.obj.hom.unop ≫ a.unop)
    infer_instance)

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y) (n : ℕ)
  {A B : C} (i : A ⟶ B)

local notation "J" => MatchingIndex n
local notation "πₙ" => matchingProjection n

variable (a : (Functor.const (MatchingIndex n)).obj A ⟶ matchingProjection n ⋙ X)
  (b : (Functor.const (MatchingIndex n)).obj B ⟶ matchingProjection n ⋙ Y)

local notation "pₙ" => Functor.whiskerLeft πₙ f
local notation "degree" => (matchingDegree (n := n))

private def matchingLiftLowerCone {k : ℕ} (prev : ConeLiftBelow i pₙ a b degree k)
    (g : op ⦋n⦌ ⟶ op ⦋k⦌) (hk : k < n) [Mono g.unop] :
    Cone (matchingProjection k ⋙ X) where
  pt := B
  π :=
    { app := fun s ↦ prev.app ((matchingCompose g hk).obj s) s.property.1
      naturality := by
        intro s t e
        exact (Category.id_comp _).trans
          (prev.naturality ((matchingCompose g hk).map e) s.property.1 t.property.1).symm }

private theorem exists_matchingLiftLeg {k : ℕ}
    (comm : ∀ s, a.app s ≫ (pₙ).app s = i ≫ b.app s)
    (lift : ∀ m < n, HasLiftingProperty i (relativeMatchingMap m f))
    (prev : ConeLiftBelow i pₙ a b degree k)
    (s : J) (hs : degree s = k) :
    Nonempty (ConeLiftLeg prev s) := by
  have hr : s.obj.right = op ⦋k⦌ := congrArg Opposite.op (SimplexCategory.ext _ _ hs)
  let g := s.obj.hom ≫ eqToHom hr
  have hk : k < n := hs ▸ s.property.1
  haveI : Mono g.unop := by
    letI := s.property.2
    dsimp [g]
    infer_instance
  have he : s = matchingIndexOfArrow g hk inferInstance := matchingIndex_eq_of_right hr rfl
  rw [he]
  let c := matchingLiftLowerCone f n i a b prev g hk
  let u := limit.lift _ c
  have hcompat : u ≫ (matchingFunctor k).map f =
      b.app (matchingIndexOfArrow g hk inferInstance) ≫ (matchingComparison k).app Y := by
    apply limit.hom_ext
    intro t
    change (u ≫ limMap (Functor.whiskerLeft _ f)) ≫ limit.π _ t =
      (_ ≫ limit.lift _ (matchingCone k Y)) ≫ limit.π _ t
    simp only [Category.assoc, limMap_π, u, limit.lift_π_assoc, limit.lift_π]
    change prev.app ((matchingCompose g hk).obj t) t.property.1 ≫
        (pₙ).app ((matchingCompose g hk).obj t) = _
    rw [prev.fac_right]
    have w : 𝟙 B ≫ b.app ((matchingCompose g hk).obj t) =
        b.app (matchingIndexOfArrow g hk inferInstance) ≫ Y.map t.obj.hom := b.naturality
      (show matchingIndexOfArrow g hk inferInstance ⟶ (matchingCompose g hk).obj t from
        ⟨StructuredArrow.homMk t.obj.hom rfl⟩)
    simpa only [Category.id_comp] using w
  let l := pullback.lift u (b.app (matchingIndexOfArrow g hk inferInstance)) hcompat
  have hsq : CommSq (a.app (matchingIndexOfArrow g hk inferInstance)) i
      (relativeMatchingMap k f) l := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeMatchingMap, l, pullback.lift_fst]
      apply limit.hom_ext
      intro t
      change (_ ≫ limit.lift _ (matchingCone k X)) ≫ limit.π _ t =
        (_ ≫ limit.lift _ c) ≫ limit.π _ t
      simp only [Category.assoc, limit.lift_π]
      change _ = i ≫ prev.app ((matchingCompose g hk).obj t) t.property.1
      rw [prev.fac_left]
      have w : 𝟙 A ≫ a.app ((matchingCompose g hk).obj t) =
          a.app (matchingIndexOfArrow g hk inferInstance) ≫ X.map t.obj.hom := a.naturality
        (show matchingIndexOfArrow g hk inferInstance ⟶ (matchingCompose g hk).obj t from
          ⟨StructuredArrow.homMk t.obj.hom rfl⟩)
      simpa only [Category.id_comp] using w.symm
    · simpa only [Category.assoc, relativeMatchingMap, l, pullback.lift_snd]
        using comm (matchingIndexOfArrow g hk inferInstance)
  letI := lift k hk
  have hf := hsq.fac_right
  refine ⟨⟨hsq.lift, hsq.fac_left, ?_, ?_⟩⟩
  · simpa only [Category.assoc, relativeMatchingMap, l, pullback.lift_snd]
      using congrArg (fun z ↦ z ≫ pullback.snd _ _) hf
  · intro t e ht
    let t' : MatchingIndex k := matchingIndexOfArrow e.hom.right ht (matchingIndex_map_mono e)
    have he' : (matchingCompose g hk).obj t' = t :=
      matchingIndex_eq_of_right rfl (by
        rw [eqToHom_refl, Category.comp_id]
        exact StructuredArrow.w e.hom)
    have w : (hsq.lift ≫ relativeMatchingMap k f) ≫ pullback.fst _ _ =
        l ≫ pullback.fst _ _ := by rw [hf]
    simp only [Category.assoc, relativeMatchingMap, l, pullback.lift_fst] at w
    have wp := congrArg (fun z ↦ z ≫ limit.π (matchingProjection k ⋙ X) t') w
    have w' : hsq.lift ≫ X.map e.hom.right =
        prev.app ((matchingCompose g hk).obj t') t'.property.1 := by
      simpa only [Category.assoc, matchingComparison, u, limit.lift_π] using wp
    exact w'.trans (by congr)

/-- Right lifting against a matching-object map follows from the lower relative matching maps. -/
theorem hasLiftingProperty_matchingFunctor_map
    (lift : ∀ m < n, HasLiftingProperty i (relativeMatchingMap m f)) :
    HasLiftingProperty i ((matchingFunctor n).map f) := by
  constructor
  intro x y sq
  let a : (Functor.const J).obj A ⟶ πₙ ⋙ X :=
    (Functor.const J).map x ≫ (limit.cone (πₙ ⋙ X)).π
  let b : (Functor.const J).obj B ⟶ πₙ ⋙ Y :=
    (Functor.const J).map y ≫ (limit.cone (πₙ ⋙ Y)).π
  have comm : ∀ s, a.app s ≫ (pₙ).app s = i ≫ b.app s := by
    intro s
    have h := congrArg (fun z ↦ z ≫ limit.π (πₙ ⋙ Y) s) sq.w
    change (x ≫ limMap pₙ) ≫ _ = (i ≫ y) ≫ _ at h
    change (x ≫ limit.π (πₙ ⋙ X) s) ≫ (pₙ).app s = i ≫ y ≫ limit.π (πₙ ⋙ Y) s
    simpa only [Category.assoc, limMap_π] using h
  let d := coneLiftBelow matchingIndex_decreases
    (exists_matchingLiftLeg f n i a b comm lift) n
  let c : Cone (πₙ ⋙ X) :=
    { pt := B
      π :=
        { app := fun s ↦ d.app s s.property.1
          naturality := by
            intro s t e
            exact (Category.id_comp _).trans (d.naturality e s.property.1 t.property.1).symm } }
  refine CommSq.HasLift.mk' ⟨limit.lift _ c, ?_, ?_⟩
  · apply limit.hom_ext
    intro s
    change (i ≫ limit.lift _ c) ≫ limit.π (πₙ ⋙ X) s = x ≫ limit.π (πₙ ⋙ X) s
    simp only [Category.assoc, limit.lift_π]
    exact d.fac_left s s.property.1
  · apply limit.hom_ext
    intro s
    change (limit.lift _ c ≫ limMap pₙ) ≫ limit.π (πₙ ⋙ Y) s = y ≫ limit.π (πₙ ⋙ Y) s
    simp only [Category.assoc, limMap_π, limit.lift_π_assoc]
    exact d.fac_right s s.property.1

/-- The matching-object functor preserves a right lifting class from the lower degrees. -/
theorem matchingFunctor_map_rlp (T : MorphismProperty C)
    (hf : ∀ m < n, T.rlp (relativeMatchingMap m f)) :
    T.rlp ((matchingFunctor n).map f) :=
  fun _ _ i hi ↦ hasLiftingProperty_matchingFunctor_map f n i (fun m hm ↦ hf m hm i hi)

end

end DaggerModels.PartII
