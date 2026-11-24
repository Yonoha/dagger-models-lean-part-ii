import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! Right lifting against presentable endpoints is stable under filtered colimits. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty

universe w v u t z

namespace DaggerModels.PartII

variable {C : Type u} [Category.{v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular]
  {J : Type t} [Category.{z} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
  {F G : J ⥤ C} (p : F ⟶ G) {cF : Cocone F} {cG : Cocone G}
  (hF : IsColimit cF) (hG : IsColimit cG)
  (q : cF.pt ⟶ cG.pt) (hq : ∀ j, cF.ι.app j ≫ q = p.app j ≫ cG.ι.app j)

include hF hG hq in
/-- A square into a filtered colimit of maps factors through a commutative square at
one stage when both objects of its left map are presentable. -/
theorem hasLiftingProperty_of_filteredColimit {A B : C}
    [IsCardinalPresentable A κ] [IsCardinalPresentable B κ] (i : A ⟶ B)
    (h : ∀ j, HasLiftingProperty i (p.app j)) :
    HasLiftingProperty i q := by
  constructor
  intro a b sq
  letI : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨j, a₀, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hF a
  obtain ⟨k, b₀, hb⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hG b
  let l := IsFiltered.max j k
  let a₁ := a₀ ≫ F.map (IsFiltered.leftToMax j k)
  let b₁ := b₀ ≫ G.map (IsFiltered.rightToMax j k)
  have ha₁ : a₁ ≫ cF.ι.app l = a := by
    dsimp only [a₁, l]
    rw [Category.assoc, Cocone.w, ha]
  have hb₁ : b₁ ≫ cG.ι.app l = b := by
    dsimp only [b₁, l]
    rw [Category.assoc, Cocone.w, hb]
  have he : (a₁ ≫ p.app l) ≫ cG.ι.app l = (i ≫ b₁) ≫ cG.ι.app l := by
    rw [Category.assoc, ← hq, ← Category.assoc, ha₁, Category.assoc, hb₁, sq.w]
  obtain ⟨m, lm, hm⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hG _ _ he
  have stage : CommSq (a₁ ≫ F.map lm) i (p.app m) (b₁ ≫ G.map lm) := by
    constructor
    rw [Category.assoc, p.naturality, ← Category.assoc, hm, Category.assoc]
  letI := h m
  refine CommSq.HasLift.mk' ⟨stage.lift ≫ cF.ι.app m, ?_, ?_⟩
  · rw [← Category.assoc, stage.fac_left, Category.assoc, Cocone.w, ha₁]
  · rw [Category.assoc, hq, ← Category.assoc, stage.fac_right, Category.assoc, Cocone.w, hb₁]

include hF hG hq in
/-- The right lifting class of a family with presentable endpoints is preserved
by filtered colimits of arrows. -/
theorem rlp_of_filteredColimit (I : MorphismProperty C)
    (hI : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ ∧ IsCardinalPresentable B κ)
    (hp : ∀ j, I.rlp (p.app j)) : I.rlp q := by
  intro A B i hi
  letI := (hI i hi).1
  letI := (hI i hi).2
  exact hasLiftingProperty_of_filteredColimit (κ := κ) p hF hG q hq i (fun j ↦ hp j i hi)

end DaggerModels.PartII
