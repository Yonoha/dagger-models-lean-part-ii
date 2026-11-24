import DaggerModelsPartII.ReedyMaps
import DaggerModelsPartII.RankedConeLifting
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! Lifting from the map of latching objects using lower relative latching maps. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

private def latchingIndexOfArrow {n : ℕ} {s : SimplexCategoryᵒᵖ}
    (a : s ⟶ op ⦋n⦌) (hs : s.unop.len < n) (ha : Epi a.unop) : LatchingIndex n :=
  ⟨CostructuredArrow.mk a, hs, ha⟩

private theorem latchingIndex_eq_of_left {n : ℕ} {s t : LatchingIndex n}
    (h : s.obj.left = t.obj.left) (w : s.obj.hom = eqToHom h ≫ t.obj.hom) : s = t :=
  ObjectProperty.FullSubcategory.ext (CostructuredArrow.obj_ext _ _ h w.symm)

private def latchingDegree {n : ℕ} (s : (LatchingIndex n)ᵒᵖ) : ℕ :=
  s.unop.obj.left.unop.len

private theorem simplexOp_eqToHom_of_unop_epi {s t : SimplexCategoryᵒᵖ}
    (a : s ⟶ t) (h : s = t) [Epi a.unop] : a = eqToHom h := by
  subst t
  apply Quiver.Hom.unop_inj
  exact SimplexCategory.eq_id_of_epi a.unop

private theorem latchingIndexOp_decreases {n : ℕ} {s t : (LatchingIndex n)ᵒᵖ}
    (f : s ⟶ t) :
    latchingDegree t < latchingDegree s ∨ ∃ h : s = t, f = eqToHom h := by
  letI := latchingIndex_map_epi f.unop
  rcases lt_or_eq_of_le (SimplexCategory.len_le_of_epi f.unop.hom.left.unop) with h | h
  · exact Or.inl h
  · have hl : t.unop.obj.left = s.unop.obj.left :=
      congrArg op (SimplexCategory.ext _ _ h)
    have hf := simplexOp_eqToHom_of_unop_epi f.unop.hom.left hl
    have he : t.unop = s.unop :=
      latchingIndex_eq_of_left hl (hf ▸ (CostructuredArrow.w f.unop.hom).symm)
    right
    refine ⟨(congrArg op he).symm, ?_⟩
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    rw [hf]
    have ht : s = t := (congrArg op he).symm
    subst t
    rfl

/-- Compose a proper degeneracy index of `[k]` with one of `[n]`. -/
private def latchingCompose {n k : ℕ} (a : op ⦋k⦌ ⟶ op ⦋n⦌)
    (hk : k < n) [Epi a.unop] : LatchingIndex k ⥤ LatchingIndex n :=
  ObjectProperty.lift _ ((latchingIndexProperty k).ι ⋙ CostructuredArrow.map a) (fun s ↦ by
    refine ⟨lt_trans s.property.1 hk, ?_⟩
    letI := s.property.2
    change Epi (a.unop ≫ s.obj.hom.unop)
    infer_instance)

noncomputable section

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y) (n : ℕ)
  {U V : C} (p : U ⟶ V)

variable (a : latchingProjection n ⋙ X ⟶ (Functor.const (LatchingIndex n)).obj U)
  (b : latchingProjection n ⋙ Y ⟶ (Functor.const (LatchingIndex n)).obj V)

local notation "J" => LatchingIndex n
local notation "πₙ" => latchingProjection n
local notation "fₙ" => Functor.whiskerLeft πₙ f
local notation "degree" => (latchingDegree (n := n))

private def latchingLiftLowerCocone {k : ℕ}
    (prev : ConeLiftBelow p.op (NatTrans.op fₙ) (NatTrans.op b) (NatTrans.op a) degree k)
    (g : op ⦋k⦌ ⟶ op ⦋n⦌) (hk : k < n) [Epi g.unop] :
    Cocone (latchingProjection k ⋙ Y) where
  pt := U
  ι :=
    { app := fun s ↦ (prev.app (op ((latchingCompose g hk).obj s)) s.property.1).unop
      naturality := by
        intro s t e
        exact (Quiver.Hom.op_inj
          (prev.naturality ((latchingCompose g hk).map e).op t.property.1 s.property.1)).trans
            (Category.comp_id _).symm }

private theorem exists_latchingLiftLeg {k : ℕ}
    (comm : ∀ s, a.app s ≫ p = (fₙ).app s ≫ b.app s)
    (lift : ∀ m < n, HasLiftingProperty (relativeLatchingMap m f) p)
    (prev : ConeLiftBelow p.op (NatTrans.op fₙ) (NatTrans.op b) (NatTrans.op a) degree k)
    (s : Jᵒᵖ) (hs : degree s = k) :
    Nonempty (ConeLiftLeg prev s) := by
  have hl : op ⦋k⦌ = s.unop.obj.left := congrArg op (SimplexCategory.ext _ _ hs.symm)
  let g := eqToHom hl ≫ s.unop.obj.hom
  have hk : k < n := hs ▸ s.unop.property.1
  haveI : Epi g.unop := by
    letI := s.unop.property.2
    dsimp [g]
    infer_instance
  have he : latchingIndexOfArrow g hk inferInstance = s.unop :=
    latchingIndex_eq_of_left hl rfl
  have he' : s = op (latchingIndexOfArrow g hk inferInstance) := (congrArg op he).symm
  rw [he']
  let c := latchingLiftLowerCocone f n p a b prev g hk
  let u := colimit.desc _ c
  have hcompat : (latchingComparison k).app X ≫
      a.app (latchingIndexOfArrow g hk inferInstance) = (latchingFunctor k).map f ≫ u := by
    apply colimit.hom_ext
    intro t
    change colimit.ι _ t ≫ (colimit.desc _ (latchingCocone k X) ≫ _) =
      colimit.ι _ t ≫ (colimMap (Functor.whiskerLeft _ f) ≫ u)
    simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, u, colimit.ι_desc]
    change _ = (fₙ).app ((latchingCompose g hk).obj t) ≫
      (prev.app (op ((latchingCompose g hk).obj t)) t.property.1).unop
    have h : (fₙ).app ((latchingCompose g hk).obj t) ≫
        (prev.app (op ((latchingCompose g hk).obj t)) t.property.1).unop =
        a.app ((latchingCompose g hk).obj t) :=
      Quiver.Hom.op_inj (prev.fac_right (op ((latchingCompose g hk).obj t)) t.property.1)
    rw [h]
    have w : X.map t.obj.hom ≫ a.app (latchingIndexOfArrow g hk inferInstance) =
        a.app ((latchingCompose g hk).obj t) ≫ 𝟙 U := a.naturality
      (show (latchingCompose g hk).obj t ⟶ latchingIndexOfArrow g hk inferInstance from
        ⟨CostructuredArrow.homMk t.obj.hom rfl⟩)
    exact w.trans (Category.comp_id _)
  let l := pushout.desc (a.app (latchingIndexOfArrow g hk inferInstance)) u hcompat
  have hsq : CommSq l (relativeLatchingMap k f) p
      (b.app (latchingIndexOfArrow g hk inferInstance)) := by
    constructor
    apply pushout.hom_ext
    · simpa only [relativeLatchingMap, l, pushout.inl_desc_assoc]
        using comm (latchingIndexOfArrow g hk inferInstance)
    · simp only [relativeLatchingMap, l, pushout.inr_desc_assoc]
      apply colimit.hom_ext
      intro t
      change colimit.ι _ t ≫ (colimit.desc _ c ≫ _) =
        colimit.ι _ t ≫ (colimit.desc _ (latchingCocone k Y) ≫ _)
      simp only [colimit.ι_desc_assoc]
      change (prev.app (op ((latchingCompose g hk).obj t)) t.property.1).unop ≫ p = _
      have h : (prev.app (op ((latchingCompose g hk).obj t)) t.property.1).unop ≫ p =
          b.app ((latchingCompose g hk).obj t) :=
        Quiver.Hom.op_inj (prev.fac_left (op ((latchingCompose g hk).obj t)) t.property.1)
      rw [h]
      have w : Y.map t.obj.hom ≫ b.app (latchingIndexOfArrow g hk inferInstance) =
          b.app ((latchingCompose g hk).obj t) ≫ 𝟙 V := b.naturality
        (show (latchingCompose g hk).obj t ⟶ latchingIndexOfArrow g hk inferInstance from
          ⟨CostructuredArrow.homMk t.obj.hom rfl⟩)
      exact (w.trans (Category.comp_id _)).symm
  letI := lift k hk
  have hf := hsq.fac_left
  refine ⟨⟨hsq.lift.op, ?_, ?_, ?_⟩⟩
  · exact Quiver.Hom.unop_inj hsq.fac_right
  · apply Quiver.Hom.unop_inj
    have w := congrArg (fun z ↦ pushout.inl _ _ ≫ z) hf
    simpa only [relativeLatchingMap, l, pushout.inl_desc_assoc, pushout.inl_desc] using w
  · intro t e ht
    let t' : LatchingIndex k := latchingIndexOfArrow e.unop.hom.left ht
      (latchingIndex_map_epi e.unop)
    have he'' : (latchingCompose g hk).obj t' = t.unop :=
      latchingIndex_eq_of_left rfl (by
        rw [eqToHom_refl, Category.id_comp]
        exact CostructuredArrow.w e.unop.hom)
    have w : pushout.inr _ _ ≫ (relativeLatchingMap k f ≫ hsq.lift) =
        pushout.inr _ _ ≫ l := by rw [hf]
    simp only [relativeLatchingMap, l, pushout.inr_desc_assoc, pushout.inr_desc] at w
    have wp := congrArg (fun z ↦ colimit.ι (latchingProjection k ⋙ Y) t' ≫ z) w
    have w' : Y.map e.unop.hom.left ≫ hsq.lift =
        (prev.app (op ((latchingCompose g hk).obj t')) t'.property.1).unop := by
      simpa only [latchingComparison, u, colimit.ι_desc_assoc, colimit.ι_desc] using wp
    exact Quiver.Hom.unop_inj (w'.trans (by congr))

/-- Left lifting from a latching-object map follows from the lower relative latching maps. -/
theorem hasLiftingProperty_latchingFunctor_map
    (lift : ∀ m < n, HasLiftingProperty (relativeLatchingMap m f) p) :
    HasLiftingProperty ((latchingFunctor n).map f) p := by
  constructor
  intro x y sq
  let a : πₙ ⋙ X ⟶ (Functor.const J).obj U :=
    (colimit.cocone (πₙ ⋙ X)).ι ≫ (Functor.const J).map x
  let b : πₙ ⋙ Y ⟶ (Functor.const J).obj V :=
    (colimit.cocone (πₙ ⋙ Y)).ι ≫ (Functor.const J).map y
  have comm : ∀ s, a.app s ≫ p = (fₙ).app s ≫ b.app s := by
    intro s
    have h := congrArg (fun z ↦ colimit.ι (πₙ ⋙ X) s ≫ z) sq.w
    change colimit.ι (πₙ ⋙ X) s ≫ (x ≫ p) = _ ≫ (colimMap fₙ ≫ y) at h
    change (colimit.ι (πₙ ⋙ X) s ≫ x) ≫ p = (fₙ).app s ≫ colimit.ι (πₙ ⋙ Y) s ≫ y
    simpa only [Category.assoc, ι_colimMap_assoc] using h
  let d := coneLiftBelow latchingIndexOp_decreases
    (exists_latchingLiftLeg f n p a b comm lift) n
  let c : Cocone (πₙ ⋙ Y) :=
    { pt := U
      ι :=
        { app := fun s ↦ (d.app (op s) s.property.1).unop
          naturality := by
            intro s t e
            exact (Quiver.Hom.op_inj (d.naturality e.op t.property.1 s.property.1)).trans
              (Category.comp_id _).symm } }
  refine CommSq.HasLift.mk' ⟨colimit.desc _ c, ?_, ?_⟩
  · apply colimit.hom_ext
    intro s
    change colimit.ι (πₙ ⋙ X) s ≫ (colimMap fₙ ≫ colimit.desc _ c) =
      colimit.ι (πₙ ⋙ X) s ≫ x
    simp only [ι_colimMap_assoc, colimit.ι_desc]
    exact Quiver.Hom.op_inj (d.fac_right (op s) s.property.1)
  · apply colimit.hom_ext
    intro s
    change colimit.ι (πₙ ⋙ Y) s ≫ (colimit.desc _ c ≫ p) = colimit.ι (πₙ ⋙ Y) s ≫ y
    simp only [colimit.ι_desc_assoc]
    exact Quiver.Hom.op_inj (d.fac_left (op s) s.property.1)

/-- The latching-object functor preserves a left lifting class from the lower degrees. -/
theorem latchingFunctor_map_llp (T : MorphismProperty C)
    (hf : ∀ m < n, T.llp (relativeLatchingMap m f)) :
    T.llp ((latchingFunctor n).map f) :=
  fun _ _ p hp ↦ hasLiftingProperty_latchingFunctor_map f n p (fun m hm ↦ hf m hm p hp)

end

end DaggerModels.PartII
