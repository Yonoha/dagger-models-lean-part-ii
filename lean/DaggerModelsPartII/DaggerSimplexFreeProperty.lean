import DaggerModelsPartII.DaggerSimplexEnrichment

/-!
# Universal property of the ordinary free dagger simplex

The path model has precisely the universal property of the free dagger category
on the chain `0 → 1 → ... → n`.  A dagger functor out of it is equivalent to
choosing the images of the vertices and the positive adjacent generators.
The images of the reverse generators and of arbitrary words are forced.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

universe u v

namespace DaggerModels.PartII.DaggerSimplexFreeProperty

variable (n : ℕ) (C : Type u) [Category.{v} C] [DaggerCategory C]

/-- Object images and positive adjacent-edge images. -/
structure ChainData where
  obj : Line n → C
  edge : ∀ {a b : Line n}, (lineQuiver n).Hom a b → (obj a ⟶ obj b)

/-- A negative edge is sent to the dagger of the corresponding positive edge. -/
def edgeValue (D : ChainData n C) {a b : Line n}
    (e : (symmLineQuiver n).Hom a b) : D.obj a ⟶ D.obj b :=
  match e with
  | Sum.inl h => D.edge h
  | Sum.inr h => dagger (D.edge h)

theorem edgeValue_swap (D : ChainData n C) {a b : Line n}
    (e : (symmLineQuiver n).Hom a b) :
    edgeValue n C D (Sum.swap e) = dagger (edgeValue n C D e) := by
  change (lineQuiver n).Hom a b ⊕ (lineQuiver n).Hom b a at e
  cases e with
  | inl h => rfl
  | inr h => simp [edgeValue]

/-- Evaluate an arbitrary finite word by composition. -/
def wordValue (D : ChainData n C) {a b : Line n}
    (p : @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a b) :
    D.obj a ⟶ D.obj b := by
  induction p with
  | nil => exact 𝟙 _
  | @cons b c p e ih => exact ih ≫ edgeValue n C D e

@[simp] theorem wordValue_nil (D : ChainData n C) (a : Line n) :
    wordValue n C D (Quiver.Path.nil :
      @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a a) = 𝟙 _ := rfl

@[simp] theorem wordValue_cons (D : ChainData n C) {a b c : Line n}
    (p : @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a b)
    (e : (symmLineQuiver n).Hom b c) :
    wordValue n C D (p.cons e) = wordValue n C D p ≫ edgeValue n C D e := rfl

theorem wordValue_comp (D : ChainData n C) {a b c : Line n}
    (p : @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a b)
    (q : @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) b c) :
    wordValue n C D (p.comp q) = wordValue n C D p ≫ wordValue n C D q := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil, wordValue_nil, Category.comp_id]
  | @cons b c q e ih =>
    rw [Quiver.Path.comp_cons, wordValue_cons, ih, wordValue_cons, Category.assoc]

theorem wordValue_dagger (D : ChainData n C) {a b : Line n}
    (p : @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a b) :
    wordValue n C D (Quiver.Path.reverse p) = dagger (wordValue n C D p) := by
  letI : Quiver (Quiver.Symmetrify (Line n)) := symmLineQuiver n
  letI : Quiver.HasInvolutiveReverse (Quiver.Symmetrify (Line n)) :=
    symmLineReverse n
  induction p with
  | nil =>
    rw [Quiver.Path.reverse, wordValue_nil]
    simp
  | @cons b c p e ih =>
    rw [Quiver.Path.reverse, wordValue_comp, wordValue_cons,
      DaggerCategory.dagger_comp, ih]
    change wordValue n C D (@Quiver.Hom.toPath _ (symmLineQuiver n) c b e.swap) ≫
      dagger (wordValue n C D p) =
        dagger (edgeValue n C D e) ≫ dagger (wordValue n C D p)
    have hsingle : wordValue n C D
        (@Quiver.Hom.toPath _ (symmLineQuiver n) c b e.swap) =
        edgeValue n C D e.swap := by
      change 𝟙 _ ≫ _ = _
      simp
    rw [hsingle, edgeValue_swap]

/-- Extend the chosen positive edge images to an actual dagger functor. -/
def extend (D : ChainData n C) : FreeDaggerSimplex n ⥤ C where
  obj X := D.obj X.vertex
  map p := wordValue n C D p
  map_id _ := rfl
  map_comp p q := wordValue_comp n C D p q

instance extend_preservesDagger (D : ChainData n C) : DaggerFunctor (extend n C D) where
  map_dagger p := wordValue_dagger n C D p

/-- A dagger functor records the images of vertices and positive edges. -/
def restrict (F : {F : FreeDaggerSimplex n ⥤ C // DaggerFunctor F}) : ChainData n C where
  obj a := F.1.obj ⟨a⟩
  edge {a b} h := F.1.map (@Quiver.Hom.toPath _ (symmLineQuiver n) a b (Sum.inl h))

theorem edgeValue_restrict
    (F : {F : FreeDaggerSimplex n ⥤ C // DaggerFunctor F})
    {a b : Line n} (e : (symmLineQuiver n).Hom a b) :
    edgeValue n C (restrict n C F) e =
      F.1.map (@Quiver.Hom.toPath _ (symmLineQuiver n) a b e) := by
  change (lineQuiver n).Hom a b ⊕ (lineQuiver n).Hom b a at e
  cases e with
  | inl h => rfl
  | inr h =>
    let _ : DaggerFunctor F.1 := F.2
    have hd := DaggerFunctor.map_dagger
      (F := F.1) (@Quiver.Hom.toPath _ (symmLineQuiver n) b a (Sum.inl h))
    simpa [restrict, edgeValue, DaggerModels.dagger,
      Quiver.Hom.toPath, Quiver.Path.reverse] using hd.symm

theorem wordValue_restrict
    (F : {F : FreeDaggerSimplex n ⥤ C // DaggerFunctor F})
    {a b : Line n}
    (p : @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a b) :
    wordValue n C (restrict n C F) p = F.1.map p := by
  letI : Quiver (Line n) := symmLineQuiver n
  induction p with
  | nil =>
    exact (F.1.map_id ⟨a⟩).symm
  | @cons b c p e ih =>
    rw [wordValue_cons, ih, edgeValue_restrict]
    have hcomp := F.1.map_comp p
      (@Quiver.Hom.toPath _ (symmLineQuiver n) b c e)
    change F.1.map p ≫ F.1.map _ = F.1.map (p.cons e)
    rw [← hcomp]
    rfl

theorem restrict_extend (D : ChainData n C) :
    restrict n C ⟨extend n C D, inferInstance⟩ = D := by
  cases D with
  | mk obj edge =>
    have hedge :
        (fun {a b : Line n} (h : (lineQuiver n).Hom a b) =>
          wordValue n C (ChainData.mk obj edge)
            (@Quiver.Hom.toPath _ (symmLineQuiver n) a b (Sum.inl h))) = @edge := by
      funext a b h
      simp [wordValue, Quiver.Hom.toPath, edgeValue]
    exact congrArg (fun e => ChainData.mk obj e) hedge

theorem extend_restrict
    (F : {F : FreeDaggerSimplex n ⥤ C // DaggerFunctor F}) :
    (⟨extend n C (restrict n C F), inferInstance⟩ :
      {G : FreeDaggerSimplex n ⥤ C // DaggerFunctor G}) = F := by
  apply Subtype.ext
  apply CategoryTheory.Functor.ext
  case a.h_obj =>
    intro X
    cases X
    rfl
  case a.h_map =>
    intro X Y p
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      wordValue_restrict n C F p

/-- The actual free dagger category universal property on the finite chain. -/
def freeDaggerSimplexHomEquiv :
    ChainData n C ≃ {F : FreeDaggerSimplex n ⥤ C // DaggerFunctor F} where
  toFun D := ⟨extend n C D, inferInstance⟩
  invFun := restrict n C
  left_inv := restrict_extend n C
  right_inv := extend_restrict n C

/-- A chain diagram also determines a functor from the ordinary finite ordinal. -/
def ordinalFunctor (D : ChainData n C) : Fin (n + 1) ⥤ C where
  obj i := D.obj (lineAt n i.val (Nat.lt_succ_iff.mp i.isLt))
  map {i j} h := wordValue n C D
    (forwardWord n i.val j.val (Nat.lt_succ_iff.mp i.isLt)
      (Nat.lt_succ_iff.mp j.isLt) (CategoryTheory.leOfHom h))
  map_id i := by
    change wordValue n C D (forwardWord n i.val i.val _ _ _) = 𝟙 _
    rw [forwardWord_self]
    rfl
  map_comp {i j k} h g := by
    change wordValue n C D (forwardWord n i.val k.val _ _ _) =
      wordValue n C D (forwardWord n i.val j.val _ _ _) ≫
        wordValue n C D (forwardWord n j.val k.val _ _ _)
    rw [← wordValue_comp]
    exact (congrArg (wordValue n C D)
      (forwardWord_comp n i.val j.val k.val _ _ _
        (CategoryTheory.leOfHom h) (CategoryTheory.leOfHom g))).symm

/-- A finite-ordinal diagram supplies the positive generators of a chain. -/
def chainOfOrdinalFunctor (F : Fin (n + 1) ⥤ C) : ChainData n C where
  obj a := F.obj ⟨a.val, a.isLt⟩
  edge {a b} h := F.map (CategoryTheory.homOfLE (show
    (⟨a.val, a.isLt⟩ : Fin (n + 1)) ≤ ⟨b.val, b.isLt⟩ from by
      change a.val ≤ b.val
      have hab : a.val + 1 = b.val := h.down
      omega))

theorem wordValue_adjacent (D : ChainData n C) {a b : Line n}
    (h : (lineQuiver n).Hom a b) :
    wordValue n C D (forwardWord n a.val b.val
      (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp b.isLt)
      (by have hab : a.val + 1 = b.val := h.down; omega)) = D.edge h := by
  have hab : a.val < b.val := by
    have hh : a.val + 1 = b.val := h.down
    omega
  have hw := intervalWord_edge n (Sum.inl h)
  rw [intervalWord_forward n a b hab.le] at hw
  rw [hw]
  change 𝟙 _ ≫ D.edge h = D.edge h
  simp

theorem chainOfOrdinalFunctor_ordinalFunctor (D : ChainData n C) :
    chainOfOrdinalFunctor n C (ordinalFunctor n C D) = D := by
  cases D with
  | mk obj edge =>
    have hedge :
        (fun {a b : Line n} (h : (lineQuiver n).Hom a b) =>
          wordValue n C (ChainData.mk obj edge)
            (forwardWord n a.val b.val (Nat.lt_succ_iff.mp a.isLt)
              (Nat.lt_succ_iff.mp b.isLt)
              (by have hab : a.val + 1 = b.val := h.down; omega))) = @edge := by
      funext a b h
      exact wordValue_adjacent n C (ChainData.mk obj edge) h
    exact congrArg (fun e => ChainData.mk obj e) hedge

theorem wordValue_ordinal (F : Fin (n + 1) ⥤ C)
    (a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≤ b) :
    wordValue n C (chainOfOrdinalFunctor n C F)
      (forwardWord n a b ha hb hab) =
        F.map (CategoryTheory.homOfLE (show
          (⟨a, by omega⟩ : Fin (n + 1)) ≤ ⟨b, by omega⟩ from hab)) := by
  induction hd : b - a using Nat.strong_induction_on generalizing a b with
  | h d ih =>
    by_cases heq : a = b
    · subst b
      rw [forwardWord_self]
      change wordValue n C (chainOfOrdinalFunctor n C F)
        (Quiver.Path.nil : @Quiver.Path (Quiver.Symmetrify (Line n))
          (symmLineQuiver n) (lineAt n a ha) (lineAt n a ha)) = _
      rw [wordValue_nil]
      have hhom : CategoryTheory.homOfLE (le_refl (⟨a, by omega⟩ : Fin (n + 1))) =
          𝟙 (⟨a, by omega⟩ : Fin (n + 1)) := Subsingleton.elim _ _
      rw [hhom, F.map_id]
      rfl
    · have hlt : a < b := lt_of_le_of_ne hab heq
      have hs : a + 1 ≤ n := by omega
      have hsb : a + 1 ≤ b := by omega
      rw [forwardWord_step n a b ha hb hlt]
      change wordValue n C (chainOfOrdinalFunctor n C F)
        (Quiver.Path.comp (forwardEdge n a hs)
          (forwardWord n (a + 1) b hs hb hsb)) = _
      rw [wordValue_comp]
      have hfirst : wordValue n C (chainOfOrdinalFunctor n C F)
          (forwardEdge n a hs) =
          F.map (CategoryTheory.homOfLE (show
            (⟨a, by omega⟩ : Fin (n + 1)) ≤ ⟨a + 1, by omega⟩ from by
              change a ≤ a + 1
              omega)) := by
        simp [forwardEdge, wordValue, Quiver.Hom.toPath,
          chainOfOrdinalFunctor, edgeValue]
      rw [hfirst, ih (b - (a + 1)) (by omega) (a + 1) b hs hb hsb (by omega)]
      have hcomp :
          CategoryTheory.homOfLE (show
            (⟨a, by omega⟩ : Fin (n + 1)) ≤ ⟨a + 1, by omega⟩ from by
              change a ≤ a + 1
              omega) ≫
              CategoryTheory.homOfLE (show
                (⟨a + 1, by omega⟩ : Fin (n + 1)) ≤ ⟨b, by omega⟩ from hsb) =
            CategoryTheory.homOfLE (show
              (⟨a, by omega⟩ : Fin (n + 1)) ≤ ⟨b, by omega⟩ from hab) :=
        Subsingleton.elim _ _
      rw [← F.map_comp, hcomp]

theorem ordinalFunctor_chainOfOrdinalFunctor (F : Fin (n + 1) ⥤ C) :
    ordinalFunctor n C (chainOfOrdinalFunctor n C F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    rfl
  case h_map =>
    intro i j h
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      wordValue_ordinal n C F i.val j.val
        (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
        (CategoryTheory.leOfHom h)

/-- A functor from `[n]` is exactly the positive chain data. -/
def chainDataOrdinalEquiv : ChainData n C ≃ (Fin (n + 1) ⥤ C) where
  toFun := ordinalFunctor n C
  invFun := chainOfOrdinalFunctor n C
  left_inv := chainOfOrdinalFunctor_ordinalFunctor n C
  right_inv := ordinalFunctor_chainOfOrdinalFunctor n C

/-- Free dagger simplex adjunction at the finite ordinal `[n]`, on ordinary targets. -/
def freeDaggerSimplexOrdinalEquiv :
    {F : FreeDaggerSimplex n ⥤ C // DaggerFunctor F} ≃ (Fin (n + 1) ⥤ C) :=
  (freeDaggerSimplexHomEquiv n C).symm.trans (chainDataOrdinalEquiv n C)

end DaggerModels.PartII.DaggerSimplexFreeProperty
