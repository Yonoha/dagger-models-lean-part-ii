import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.CategoryTheory.WithTerminal.Basic

/-! Continuous transfinite diagrams of arrows into a fixed base diagram. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty

universe u v t z

namespace DaggerModels.PartII

noncomputable section

variable {J : Type u} [LinearOrder J] [WellFoundedLT J]

private def withTopToWithTerminal : WithTop J ⥤ WithTerminal J where
  obj j := j.recTopCoe WithTerminal.star WithTerminal.of
  map {j k} f := by
    induction j using WithTop.recTopCoe <;> induction k using WithTop.recTopCoe
    · exact 𝟙 _
    · exact (WithTop.not_top_le_coe _ (leOfHom f)).elim
    · exact WithTerminal.starTerminal.from _
    · exact WithTerminal.incl.map (homOfLE (WithTop.coe_le_coe.mp (leOfHom f)))
  map_id j := by
    induction j using WithTop.recTopCoe <;> rfl
  map_comp {j k l} f g := by
    induction j using WithTop.recTopCoe <;>
      induction k using WithTop.recTopCoe <;>
        induction l using WithTop.recTopCoe <;> first
          | exact (WithTop.not_top_le_coe _ (leOfHom f)).elim
          | exact (WithTop.not_top_le_coe _ (leOfHom g)).elim
          | rfl

private theorem wellFoundedLT_withTop : WellFoundedLT (WithTop J) := by
  constructor
  refine ⟨fun a ↦ ?_⟩
  have hc (j : J) : Acc (· < ·) (j : WithTop J) := by
    refine wellFounded_lt.induction (C := fun k : J ↦ Acc (· < ·) (k : WithTop J)) j ?_
    intro j ih
    constructor
    intro i hi
    induction i using WithTop.recTopCoe
    · exact (not_lt_of_ge le_top hi).elim
    · exact ih _ (WithTop.coe_lt_coe.mp (by exact hi))
  induction a using WithTop.recTopCoe
  · constructor
    intro i hi
    induction i using WithTop.recTopCoe
    · exact (lt_irrefl _ hi).elim
    · exact hc _
  · exact hc _

private theorem hasColimitsOfShape_withTop (K : Type t) [Category.{z} K] :
    HasColimitsOfShape K (WithTop J) := by
  letI : WellFoundedLT (WithTop J) := wellFoundedLT_withTop
  constructor
  intro F
  let s := upperBounds (Set.range F.obj)
  obtain ⟨a, ha, hmin⟩ := wellFounded_lt.has_min s ⟨⊤, fun _ _ ↦ le_top⟩
  have h : IsLUB (Set.range F.obj) a := ⟨ha, fun _ hb ↦ le_of_not_gt (hmin _ hb)⟩
  exact ⟨⟨Preorder.colimitCoconeOfIsLUB F h⟩⟩

variable {C : Type t} [Category.{z} C] [HasColimitsOfSize.{u, u} C]
  {J : Type u} [LinearOrder J] [WellFoundedLT J] [SuccOrder J] [OrderBot J]

private def extendBase (K : J ⥤ C) (Z : C) (ε : K ⟶ (Functor.const J).obj Z) :
    WithTop J ⥤ C :=
  withTopToWithTerminal ⋙ WithTerminal.lift K ε.app
    (fun _ _ f ↦ (ε.naturality f).trans (Category.comp_id _))

private def indexInclusion : J ⥤ WithTop J :=
  (show Monotone (fun j : J ↦ (j : WithTop J)) from fun _ _ h ↦ WithTop.coe_le_coe.mpr h).functor

private def indexInclusionCompExtend (K : J ⥤ C) {Z : C} (ε : K ⟶ (Functor.const J).obj Z) :
    indexInclusion ⋙ extendBase K Z ε ≅ K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j f
    have he : WithTop.coe_le_coe.mp (leOfHom (indexInclusion.map f)) = leOfHom f :=
      Subsingleton.elim _ _
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change K.map (homOfLE (WithTop.coe_le_coe.mp (leOfHom (indexInclusion.map f)))) = K.map f
    congr 1)

omit [WellFoundedLT J] [SuccOrder J] [OrderBot J] in
private theorem coe_isLUB_range_Iio {j : J} (hj : Order.IsSuccLimit j) :
    IsLUB (Set.range (fun i : Set.Iio j ↦ (i.1 : WithTop J))) (j : WithTop J) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact WithTop.coe_le_coe.mpr i.2.le
  · intro b hb
    induction b using WithTop.recTopCoe with
    | top => exact le_top
    | coe b =>
      apply WithTop.coe_le_coe.mpr
      exact hj.isLUB_Iio.2 (fun i hi ↦ WithTop.coe_le_coe.mp (hb ⟨⟨i, hi⟩, rfl⟩))

/-- Construct a continuous diagram over a fixed base diagram. At each nonmaximal
index its transition and new augmentation can be prescribed by factorization. -/
theorem exists_continuous_over
    (K : J ⥤ C) {Z : C} (ε : K ⟶ (Functor.const J).obj Z)
    (P Q : MorphismProperty C) [P.RespectsIso] [Q.RespectsIso]
    {A₀ : C} (a₀ : A₀ ⟶ K.obj ⊥) (ha₀ : P a₀)
    (hs : ∀ (j : J) (_ : ¬IsMax j) (A : C) (a : A ⟶ K.obj j),
      ∃ (B : C) (i : A ⟶ B) (b : B ⟶ K.obj (Order.succ j)),
        i ≫ b = a ≫ K.map (homOfLE (Order.le_succ j)) ∧ Q i ∧ P b) :
    ∃ (G : J ⥤ C) (a : G ⟶ K), G.IsWellOrderContinuous ∧ Nonempty (G.obj ⊥ ≅ A₀) ∧ P (a.app ⊥) ∧
      ∀ (j : J), ¬IsMax j → Q (G.map (homOfLE (Order.le_succ j))) ∧ P (a.app (Order.succ j)) := by
  classical
  let H := extendBase K Z ε
  let D := Comma (𝟭 C) H
  letI : HasColimitsOfSize.{u,u} (WithTop J) := ⟨fun T _ ↦ hasColimitsOfShape_withTop T⟩
  letI : HasColimitsOfSize.{u,u} D := inferInstanceAs (HasColimitsOfSize.{u,u} (Comma (𝟭 C) H))
  let init : D := ⟨A₀, ((⊥ : J) : WithTop J), a₀⟩
  let advance (d : D) (hd : ∃ j : J, d.right = (j : WithTop J) ∧ ¬IsMax j) :
      Σ e : D, d ⟶ e := by
    let j := hd.choose
    let hidx := hd.choose_spec.1
    let a : d.left ⟶ K.obj j := d.hom ≫ H.map (eqToHom hidx)
    let f := hs j hd.choose_spec.2 d.left a
    let B := f.choose
    let i := f.choose_spec.choose
    let b := f.choose_spec.choose_spec.choose
    let e : D := ⟨B, (Order.succ j : J), b⟩
    refine ⟨e, ⟨i, eqToHom hidx ≫ indexInclusion.map (homOfLE (Order.le_succ j)), ?_⟩⟩
    change i ≫ b = d.hom ≫ H.map
      (eqToHom hidx ≫ indexInclusion.map (homOfLE (Order.le_succ j)))
    rw [H.map_comp, ← Category.assoc]
    exact f.choose_spec.choose_spec.choose_spec.1
  let step (d : D) : Σ e : D, d ⟶ e :=
    if hd : ∃ j : J, d.right = (j : WithTop J) ∧ ¬IsMax j then advance d hd else ⟨d, 𝟙 d⟩
  let Φ : SmallObject.SuccStruct D := ⟨init, fun d ↦ (step d).1, fun d ↦ (step d).2⟩
  let E := Φ.iterationFunctor J
  let G := E ⋙ Comma.fst (𝟭 C) H
  let B := E ⋙ Comma.snd (𝟭 C) H
  letI : B.IsWellOrderContinuous := by
    constructor
    intro j hj
    exact ⟨isColimitOfPreserves (Comma.snd (𝟭 C) H) (E.isColimitOfIsWellOrderContinuous j hj)⟩
  letI : G.IsWellOrderContinuous := by
    constructor
    intro j hj
    exact ⟨isColimitOfPreserves (Comma.fst (𝟭 C) H) (E.isColimitOfIsWellOrderContinuous j hj)⟩
  have hstep (d : D) (j : J) (hj : ¬IsMax j) (hd : d.right = (j : WithTop J)) :
      (Φ.succ d).right = ((Order.succ j : J) : WithTop J) ∧
        Q (Φ.toSucc d).left ∧ P (Φ.succ d).hom := by
    have h : ∃ k : J, d.right = (k : WithTop J) ∧ ¬IsMax k := ⟨j, hd, hj⟩
    change (step d).1.right = _ ∧ Q (step d).2.left ∧ P (step d).1.hom
    rw [show step d = advance d h from dif_pos h]
    have eq : h.choose = j := WithTop.coe_injective (h.choose_spec.1.symm.trans hd)
    refine ⟨congrArg (fun k : J ↦ ((Order.succ k : J) : WithTop J)) eq, ?_⟩
    exact (hs h.choose h.choose_spec.2 d.left
      (d.hom ≫ H.map (eqToHom h.choose_spec.1))).choose_spec.choose_spec.choose_spec.2
  have hB (j : J) : B.obj j = (j : WithTop J) := by
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
      obtain rfl : j = ⊥ := le_antisymm (hj bot_le) bot_le
      exact le_antisymm (leOfHom ((Comma.snd (𝟭 C) H).map (Φ.iterationFunctorObjBotIso J).hom))
        (leOfHom ((Comma.snd (𝟭 C) H).map (Φ.iterationFunctorObjBotIso J).inv))
    | succ j hj ih =>
      have hi := (Comma.snd (𝟭 C) H).mapIso (Φ.iterationFunctorObjSuccIso j hj)
      have he : B.obj (Order.succ j) = (Φ.succ (E.obj j)).right :=
        le_antisymm (leOfHom hi.hom) (leOfHom hi.inv)
      exact he.trans (hstep (E.obj j) j hj ih).1
    | isSuccLimit j hj ih =>
      have hL := Preorder.isLUB_of_isColimit _ (B.isColimitOfIsWellOrderContinuous j hj)
      have he : Set.range ((Set.principalSegIio j).monotone.functor ⋙ B).obj =
          Set.range (fun i : Set.Iio j ↦ (i.1 : WithTop J)) := by
        congr 1
        funext i
        exact ih _ i.2
      rw [he] at hL
      exact hL.unique (coe_isLUB_range_Iio hj)
  let e : B ≅ indexInclusion := NatIso.ofComponents (fun j ↦ eqToIso (hB j))
    (by intros; apply Subsingleton.elim)
  let a : G ⟶ K :=
    (show G ⟶ B ⋙ H from
      { app := fun j ↦ (E.obj j).hom
        naturality := fun _ _ f ↦ (E.map f).w }) ≫
      (Functor.isoWhiskerRight e H).hom ≫ (indexInclusionCompExtend K ε).hom
  have ha (j : J) : a.app j = (E.obj j).hom ≫ H.map (eqToHom (hB j)) := by
    change _ = _
    simp [a, indexInclusionCompExtend, e]
    exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)
  refine ⟨G, a, inferInstance,
    ⟨(Comma.fst (𝟭 C) H).mapIso (Φ.iterationFunctorObjBotIso J)⟩, ?_, ?_⟩
  · let b := Φ.iterationFunctorObjBotIso J
    have h := b.hom.w
    change b.hom.left ≫ a₀ = (E.obj ⊥).hom ≫ H.map b.hom.right at h
    rw [ha, show eqToHom (hB ⊥) = b.hom.right from Subsingleton.elim _ _, ← h]
    exact (P.cancel_left_of_respectsIso _ _).mpr ha₀
  · intro j hj
    let b := Φ.iterationFunctorObjSuccIso j hj
    have hs' := hstep (E.obj j) j hj (hB j)
    have hq : Q (G.map (homOfLE (Order.le_succ j))) := by
      change Q ((E.map (homOfLE (Order.le_succ j))).left)
      rw [Φ.iterationFunctor_map_succ j hj]
      exact (Q.cancel_right_of_respectsIso _ b.inv.left).mpr hs'.2.1
    refine ⟨hq, ?_⟩
    have h := b.hom.w
    rw [ha]
    have he : eqToHom (hB (Order.succ j)) =
        b.hom.right ≫ eqToHom hs'.1 := Subsingleton.elim _ _
    rw [he, H.map_comp, ← Category.assoc, ← h, Category.assoc]
    apply (P.cancel_left_of_respectsIso _ _).mpr
    exact (P.cancel_right_of_respectsIso _ _).mpr hs'.2.2

end

end DaggerModels.PartII
