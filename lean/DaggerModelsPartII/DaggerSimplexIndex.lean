import DaggerModels.ReverseSimplex
import DaggerModels.DaggerCategory
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The free dagger simplex index

The free dagger simplex on `[n]` is the path category on the bidirected
adjacent-edge quiver.  Its morphisms are actual finite words; no cancellation
relations are imposed between an edge and its dagger.
-/

open CategoryTheory

namespace DaggerModelsPartII.DaggerSimplexIndex

/-- The directed line quiver with vertices `0,...,n`. -/
structure Line (n : ℕ) where
  val : ℕ
  isLt : val < n + 1

/-- A vertex specified by its natural-number coordinate. -/
def lineAt (n a : ℕ) (ha : a ≤ n) : Line n := ⟨a, by omega⟩

@[simp] theorem lineAt_val (n a : ℕ) (ha : a ≤ n) :
    (lineAt n a ha).val = a := rfl

def lineQuiver (n : ℕ) : Quiver (Line n) where
  Hom i j := PLift (i.val + 1 = j.val)

instance symmLineQuiver (n : ℕ) : Quiver (Quiver.Symmetrify (Line n)) :=
  @Quiver.symmetrifyQuiver (Line n) (lineQuiver n)

def symmLineReverse (n : ℕ) :
    @Quiver.HasInvolutiveReverse (Quiver.Symmetrify (Line n)) (symmLineQuiver n) := by
  letI : Quiver (Quiver.Symmetrify (Line n)) := symmLineQuiver n
  exact { toHasReverse := ⟨fun e => e.swap⟩
          inv' := by intro _ _ e; cases e <;> rfl }

/-- The free dagger category on the directed line quiver. -/
structure FreeDaggerSimplex (n : ℕ) where
  vertex : Line n

instance freeDaggerSimplexCategory (n : ℕ) : SmallCategory (FreeDaggerSimplex n) := by
  letI : Quiver (Quiver.Symmetrify (Line n)) := symmLineQuiver n
  exact {
    Hom X Y := @Quiver.Path (Quiver.Symmetrify (Line n))
      (symmLineQuiver n) X.vertex Y.vertex
    id _ := Quiver.Path.nil
    comp f g := Quiver.Path.comp f g
    id_comp f := Quiver.Path.nil_comp f
    comp_id f := Quiver.Path.comp_nil f
    assoc f g h := Quiver.Path.comp_assoc f g h }

instance freeDaggerSimplexDagger (n : ℕ) :
    DaggerModels.DaggerCategory (FreeDaggerSimplex n) := by
  letI : Quiver (Quiver.Symmetrify (Line n)) := symmLineQuiver n
  letI : Quiver.HasInvolutiveReverse (Quiver.Symmetrify (Line n)) :=
    symmLineReverse n
  exact {
    dagger := fun f => Quiver.Path.reverse f
    dagger_involutive := fun f => Quiver.Path.reverse_reverse f
    dagger_id := fun _ => by rfl
    dagger_comp := fun f g => by
      change (Quiver.Path.comp f g).reverse =
        (Quiver.Path.reverse g).comp (Quiver.Path.reverse f)
      exact Quiver.Path.reverse_comp f g }

/-- The positive generator from `a` to `a+1`. -/
def forwardEdge (n a : ℕ) (h : a + 1 ≤ n) :
    (⟨⟨a, by omega⟩⟩ : FreeDaggerSimplex n) ⟶
      (⟨⟨a + 1, by omega⟩⟩ : FreeDaggerSimplex n) := by
  exact @Quiver.Hom.toPath (Quiver.Symmetrify (Line n))
    (symmLineQuiver n)
    (⟨a, by omega⟩ : Quiver.Symmetrify (Line n))
    (⟨a + 1, by omega⟩ : Quiver.Symmetrify (Line n))
    (Sum.inl (PLift.up rfl))

/-- The forward word along the interval from `a` to `b`. -/
def forwardWord (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≤ b) :
    (⟨⟨a, by omega⟩⟩ : FreeDaggerSimplex n) ⟶
      (⟨⟨b, by omega⟩⟩ : FreeDaggerSimplex n) := by
  by_cases heq : a = b
  · subst b
    exact 𝟙 _
  · have hstep : a + 1 ≤ b := by omega
    have hs : a + 1 ≤ n := by omega
    exact forwardEdge n a hs ≫
      forwardWord n (a + 1) b hs hb hstep
termination_by b - a

@[simp] theorem forwardWord_self (n a : ℕ) (ha : a ≤ n) :
    forwardWord n a a ha ha le_rfl = 𝟙 _ := by
  rw [forwardWord.eq_1]
  simp

theorem forwardWord_step (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n)
    (hab : a < b) :
    forwardWord n a b ha hb hab.le =
      forwardEdge n a (by omega : a + 1 ≤ n) ≫
        forwardWord n (a + 1) b (by omega) hb (by omega) := by
  rw [forwardWord.eq_1]
  simp [Nat.ne_of_lt hab]

theorem forwardWord_comp (n a b c : ℕ) (ha : a ≤ n) (hb : b ≤ n)
    (hc : c ≤ n) (hab : a ≤ b) (hbc : b ≤ c) :
    forwardWord n a b ha hb hab ≫ forwardWord n b c hb hc hbc =
      forwardWord n a c ha hc (hab.trans hbc) := by
  induction hd : b - a using Nat.strong_induction_on generalizing a b c with
  | h d ih =>
    by_cases heq : a = b
    · subst b
      simp
    · have hlt : a < b := lt_of_le_of_ne hab heq
      have hstep : a + 1 ≤ b := by omega
      rw [forwardWord_step n a b ha hb hlt,
        forwardWord_step n a c ha hc (lt_of_lt_of_le hlt hbc), Category.assoc]
      congr 1
      exact ih (b - (a + 1)) (by omega) (a + 1) b c
        (by omega) hb hc hstep hbc (by omega)

/-- The canonical monotone word between any two vertices, going forward or backward. -/
def intervalWord (n : ℕ) (a b : Line n) :
    (⟨a⟩ : FreeDaggerSimplex n) ⟶ (⟨b⟩ : FreeDaggerSimplex n) :=
  if h : a.val ≤ b.val then
    forwardWord n a.val b.val (Nat.lt_succ_iff.mp a.isLt)
      (Nat.lt_succ_iff.mp b.isLt) h
  else
    DaggerModels.dagger (forwardWord n b.val a.val
      (Nat.lt_succ_iff.mp b.isLt) (Nat.lt_succ_iff.mp a.isLt) (by omega))

theorem intervalWord_forward (n : ℕ) (a b : Line n) (h : a.val ≤ b.val) :
    intervalWord n a b = forwardWord n a.val b.val
      (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp b.isLt) h := by
  simp [intervalWord, h]

@[simp] theorem intervalWord_self (n : ℕ) (a : Line n) :
    intervalWord n a a = 𝟙 _ := by
  rw [intervalWord_forward n a a le_rfl]
  exact forwardWord_self n a.val (Nat.lt_succ_iff.mp a.isLt)

theorem intervalWord_backward (n : ℕ) (a b : Line n) (h : b.val < a.val) :
    intervalWord n a b =
      DaggerModels.dagger
        (forwardWord n b.val a.val (Nat.lt_succ_iff.mp b.isLt)
          (Nat.lt_succ_iff.mp a.isLt) h.le) := by
  simp [intervalWord, Nat.not_le_of_gt h]

theorem intervalWord_backward_le (n : ℕ) (a b : Line n)
    (h : b.val ≤ a.val) :
    intervalWord n a b = DaggerModels.dagger
      (forwardWord n b.val a.val (Nat.lt_succ_iff.mp b.isLt)
        (Nat.lt_succ_iff.mp a.isLt) h) := by
  by_cases heq : a.val = b.val
  · have hab : a = b := by
      cases a with
      | mk av ah =>
        cases b with
        | mk bv bh =>
          dsimp at heq
          subst bv
          rfl
    subst b
    rw [intervalWord_self, forwardWord_self]
    simp
  · exact intervalWord_backward n a b (lt_of_le_of_ne h (Ne.symm heq))

theorem intervalWord_dagger (n : ℕ) (a b : Line n) :
    DaggerModels.dagger (intervalWord n a b) = intervalWord n b a := by
  rcases lt_trichotomy a.val b.val with h | h | h
  · rw [intervalWord_forward n a b h.le,
      intervalWord_backward n b a h]
  · have hab : a = b := by
      cases a with
      | mk av ah =>
        cases b with
        | mk bv bh =>
          dsimp at h
          subst bv
          rfl
    subst b
    rw [intervalWord_forward n a a le_rfl]
    simp
  · rw [intervalWord_backward n a b h,
      intervalWord_forward n b a h.le]
    simp

theorem intervalWord_comp_mono (n : ℕ) (a b c : Line n)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    intervalWord n a b ≫ intervalWord n b c = intervalWord n a c := by
  rw [intervalWord_forward n a b hab, intervalWord_forward n b c hbc,
    intervalWord_forward n a c (hab.trans hbc)]
  exact forwardWord_comp n a.val b.val c.val
    (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp b.isLt)
    (Nat.lt_succ_iff.mp c.isLt) hab hbc

theorem intervalWord_comp_anti (n : ℕ) (a b c : Line n)
    (hab : b.val ≤ a.val) (hbc : c.val ≤ b.val) :
    intervalWord n a b ≫ intervalWord n b c = intervalWord n a c := by
  rw [← intervalWord_dagger n b a, ← intervalWord_dagger n c b,
    ← intervalWord_dagger n c a, ← DaggerModels.DaggerCategory.dagger_comp]
  congr 1
  exact intervalWord_comp_mono n c b a hbc hab

/-- The vertex map of an order-preserving or order-reversing ordinal map. -/
def mapLine {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (a : Line m.len) : Line n.len :=
  ⟨(f.toFun ⟨a.val, a.isLt⟩).val, (f.toFun ⟨a.val, a.isLt⟩).isLt⟩

@[simp] theorem mapLine_id (n : DaggerModels.ReverseSimplex) (a : Line n.len) :
    mapLine (𝟙 n) a = a := by cases a; rfl

@[simp] theorem mapLine_comp {m n p : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (g : n ⟶ p) (a : Line m.len) :
    mapLine (f ≫ g) a = mapLine g (mapLine f a) := rfl

/-- Substitute an interval word for every letter of a free dagger word. -/
def mapPath {m n : DaggerModels.ReverseSimplex} (f : m ⟶ n)
    {a b : Line m.len}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a b) :
    (⟨mapLine f a⟩ : FreeDaggerSimplex n.len) ⟶
      (⟨mapLine f b⟩ : FreeDaggerSimplex n.len) := by
  induction p with
  | nil => exact 𝟙 _
  | @cons b c p e ih =>
    exact ih ≫ intervalWord n.len (mapLine f b) (mapLine f c)

@[simp] theorem mapPath_nil {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (a : Line m.len) :
    mapPath f (Quiver.Path.nil :
      @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a a) = 𝟙 _ := rfl

@[simp] theorem mapPath_cons {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) {a b c : Line m.len}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a b)
    (e : (symmLineQuiver m.len).Hom b c) :
    mapPath f (Quiver.Path.cons p e) =
      mapPath f p ≫ intervalWord n.len (mapLine f b) (mapLine f c) := rfl

theorem mapPath_comp {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) {a b c : Line m.len}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a b)
    (q : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) b c) :
    mapPath f (p.comp q) = mapPath f p ≫ mapPath f q := by
  induction q with
  | nil =>
    rw [Quiver.Path.comp_nil, mapPath_nil, Category.comp_id]
  | @cons b c q e ih =>
    rw [Quiver.Path.comp_cons, mapPath_cons, ih, mapPath_cons, Category.assoc]

theorem mapPath_dagger {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) {a b : Line m.len}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a b) :
    mapPath f (Quiver.Path.reverse p) = DaggerModels.dagger (mapPath f p) := by
  letI : Quiver (Quiver.Symmetrify (Line m.len)) := symmLineQuiver m.len
  letI : Quiver.HasInvolutiveReverse (Quiver.Symmetrify (Line m.len)) :=
    symmLineReverse m.len
  induction p with
  | nil =>
    rw [Quiver.Path.reverse, mapPath_nil]
    simp
  | @cons b c p e ih =>
    rw [Quiver.Path.reverse, mapPath_comp, mapPath_cons,
      DaggerModels.DaggerCategory.dagger_comp, ih]
    change mapPath f (@Quiver.Hom.toPath _ (symmLineQuiver m.len) c b e.swap) ≫
        DaggerModels.dagger (mapPath f p) =
      DaggerModels.dagger (intervalWord n.len (mapLine f b) (mapLine f c)) ≫
        DaggerModels.dagger (mapPath f p)
    have hsingle : mapPath f (@Quiver.Hom.toPath _ (symmLineQuiver m.len) c b e.swap) =
        intervalWord n.len (mapLine f c) (mapLine f b) := by
      change 𝟙 _ ≫ _ = _
      simp
    rw [hsingle, intervalWord_dagger]

/-- The dagger functor determined by an ordinal map, with the manuscript's word formula. -/
def ordinalDaggerFunctor {m n : DaggerModels.ReverseSimplex} (f : m ⟶ n) :
    FreeDaggerSimplex m.len ⥤ FreeDaggerSimplex n.len where
  obj X := ⟨mapLine f X.vertex⟩
  map p := mapPath f p
  map_id X := by rfl
  map_comp p q := mapPath_comp f p q

instance ordinalDaggerFunctor_preservesDagger {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) : DaggerModels.DaggerFunctor (ordinalDaggerFunctor f) where
  map_dagger p := mapPath_dagger f p

theorem mapPath_forwardEdge {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (a : ℕ) (ha : a + 1 ≤ m.len) :
    mapPath f (forwardEdge m.len a ha) =
      intervalWord n.len
        (mapLine f (lineAt m.len a (by omega)))
        (mapLine f (lineAt m.len (a + 1) ha)) := by
  simp [forwardEdge, mapPath, Quiver.Hom.toPath, lineAt]

theorem mapLine_mono {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (hf : Monotone f.toFun) {a b : Line m.len}
    (hab : a.val ≤ b.val) :
    (mapLine f a).val ≤ (mapLine f b).val := by
  exact hf hab

theorem mapLine_anti {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (hf : Antitone f.toFun) {a b : Line m.len}
    (hab : a.val ≤ b.val) :
    (mapLine f b).val ≤ (mapLine f a).val := by
  exact hf hab

theorem mapPath_forwardWord {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (a b : ℕ) (ha : a ≤ m.len) (hb : b ≤ m.len)
    (hab : a ≤ b) :
    mapPath f (forwardWord m.len a b ha hb hab) =
      intervalWord n.len (mapLine f (lineAt m.len a ha))
        (mapLine f (lineAt m.len b hb)) := by
  induction hd : b - a using Nat.strong_induction_on generalizing a b with
  | h d ih =>
    by_cases heq : a = b
    · subst b
      rw [forwardWord_self]
      change mapPath f (Quiver.Path.nil :
        @Quiver.Path (Quiver.Symmetrify (Line m.len))
          (symmLineQuiver m.len) (lineAt m.len a ha) (lineAt m.len a ha)) = _
      simp
    · have hlt : a < b := lt_of_le_of_ne hab heq
      have hs : a + 1 ≤ m.len := by omega
      have hsb : a + 1 ≤ b := by omega
      rw [forwardWord_step m.len a b ha hb hlt]
      change mapPath f (Quiver.Path.comp (forwardEdge m.len a hs)
        (forwardWord m.len (a + 1) b hs hb hsb)) = _
      rw [mapPath_comp, mapPath_forwardEdge,
        ih (b - (a + 1)) (by omega) (a + 1) b hs hb hsb (by omega)]
      rcases f.monotone_or_antitone with hf | hf
      · exact intervalWord_comp_mono n.len _ _ _
          (mapLine_mono f hf (by simp only [lineAt_val]; omega))
          (mapLine_mono f hf (by simpa only [lineAt_val] using hsb))
      · exact intervalWord_comp_anti n.len _ _ _
          (mapLine_anti f hf (by simp only [lineAt_val]; omega))
          (mapLine_anti f hf (by simpa only [lineAt_val] using hsb))

theorem mapPath_intervalWord {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (a b : Line m.len) :
    mapPath f (intervalWord m.len a b) =
      intervalWord n.len (mapLine f a) (mapLine f b) := by
  by_cases h : a.val ≤ b.val
  · rw [intervalWord_forward m.len a b h]
    simpa only [lineAt] using mapPath_forwardWord f a.val b.val
      (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp b.isLt) h
  · have hlt : b.val < a.val := by omega
    rw [intervalWord_backward m.len a b hlt]
    change mapPath f (Quiver.Path.reverse
      (forwardWord m.len b.val a.val (Nat.lt_succ_iff.mp b.isLt)
        (Nat.lt_succ_iff.mp a.isLt) hlt.le)) = _
    rw [mapPath_dagger, mapPath_forwardWord, intervalWord_dagger]
    simp only [lineAt]

theorem intervalWord_edge (n : ℕ) {a b : Line n}
    (e : (symmLineQuiver n).Hom a b) :
    intervalWord n a b =
      @Quiver.Hom.toPath (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a b e := by
  cases e with
  | inl h =>
    have hab : a.val + 1 = b.val := h.down
    have hlt : a.val < b.val := by omega
    rw [intervalWord_forward n a b hlt.le]
    cases a with
    | mk av ah =>
      cases b with
      | mk bv bh =>
        dsimp at hab
        subst bv
        rw [forwardWord_step]
        simp [forwardEdge, Quiver.Hom.toPath]
        · cases h
          rfl
        · omega
  | inr h =>
    have hba : b.val + 1 = a.val := h.down
    have hlt : b.val < a.val := by omega
    rw [intervalWord_backward n a b hlt]
    cases a with
    | mk av ah =>
      cases b with
      | mk bv bh =>
        dsimp at hba
        subst av
        rw [forwardWord_step]
        simp [forwardEdge, Quiver.Hom.toPath, DaggerModels.dagger]
        · cases h
          rfl
        · omega

theorem mapPath_id {m : DaggerModels.ReverseSimplex}
    {a b : Line m.len}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a b) :
    mapPath (𝟙 m) p = p := by
  letI : Quiver (Line m.len) := symmLineQuiver m.len
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
    rw [mapPath_cons, ih]
    change p ≫ intervalWord m.len b c = p.cons e
    rw [intervalWord_edge m.len e]
    change p.comp (Quiver.Path.nil.cons e) = p.cons e
    rw [Quiver.Path.comp_cons, Quiver.Path.comp_nil]

theorem mapPath_compOrdinal {m n p : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (g : n ⟶ p) {a b : Line m.len}
    (q : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a b) :
    mapPath (f ≫ g) q = mapPath g (mapPath f q) := by
  induction q with
  | nil => rfl
  | @cons b c q e ih =>
    rw [mapPath_cons, mapPath_cons]
    change _ = mapPath g (Quiver.Path.comp (mapPath f q)
      (intervalWord n.len (mapLine f b) (mapLine f c)))
    rw [mapPath_comp, ih, mapPath_intervalWord]
    rfl

/-- An object of the small index category of free dagger simplices. -/
structure DaggerSimplex where
  len : ℕ

/-- A morphism in the free dagger simplex index is an actual dagger functor. -/
structure DaggerSimplex.Hom (m n : DaggerSimplex) where
  toFunctor : FreeDaggerSimplex m.len ⥤ FreeDaggerSimplex n.len
  map_dagger : DaggerModels.DaggerFunctor toFunctor

@[ext] theorem DaggerSimplex.Hom.ext {m n : DaggerSimplex}
    {f g : DaggerSimplex.Hom m n} (h : f.toFunctor = g.toFunctor) : f = g := by
  cases f with
  | mk F hF =>
    cases g with
    | mk G hG =>
      dsimp at h
      cases h
      rfl

instance DaggerSimplex.category : SmallCategory DaggerSimplex where
  Hom := DaggerSimplex.Hom
  id _ := ⟨𝟭 _, ⟨by intro _ _ f; rfl⟩⟩
  comp f g := ⟨f.toFunctor ⋙ g.toFunctor, ⟨by
    intro X Y h
    let _ : DaggerModels.DaggerFunctor f.toFunctor := f.map_dagger
    let _ : DaggerModels.DaggerFunctor g.toFunctor := g.map_dagger
    change g.toFunctor.map (f.toFunctor.map (DaggerModels.dagger h)) =
      DaggerModels.dagger (g.toFunctor.map (f.toFunctor.map h))
    rw [DaggerModels.DaggerFunctor.map_dagger, DaggerModels.DaggerFunctor.map_dagger]⟩⟩
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- The map on morphisms in the change-of-index functor. -/
def ordinalHom {m n : DaggerModels.ReverseSimplex} (f : m ⟶ n) :
    (⟨m.len⟩ : DaggerSimplex) ⟶ (⟨n.len⟩ : DaggerSimplex) :=
  ⟨ordinalDaggerFunctor f, inferInstance⟩

/-- The change-of-index functor `u : Δ_rev → Δ_dagger`. -/
def u : DaggerModels.ReverseSimplex ⥤ DaggerSimplex where
  obj n := ⟨n.len⟩
  map f := ordinalHom f
  map_id n := by
    apply DaggerSimplex.Hom.ext
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro X
      cases X
      rfl
    case h_map =>
      intro X Y p
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using mapPath_id p
  map_comp f g := by
    apply DaggerSimplex.Hom.ext
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro X
      cases X
      rfl
    case h_map =>
      intro X Y p
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
        mapPath_compOrdinal f g p

@[simp] theorem u_obj_len (n : DaggerModels.ReverseSimplex) :
    (u.obj n).len = n.len := rfl

@[simp] theorem u_map_obj {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (a : Line m.len) :
    ((u.map f).toFunctor.obj (⟨a⟩ : FreeDaggerSimplex m.len)).vertex =
      mapLine f a := rfl

theorem u_map_path {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) {a b : Line m.len}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m.len)) (symmLineQuiver m.len) a b) :
    (u.map f).toFunctor.map p = mapPath f p := rfl

/-- The change-of-index functor is bijective on the literal object sets. -/
theorem u_obj_bijective : Function.Bijective u.obj := by
  constructor
  · intro m n h
    cases m with
    | mk m =>
      cases n with
      | mk n =>
        cases h
        rfl
  · intro n
    exact ⟨⟨n.len⟩, rfl⟩

/-- Distinct ordinal maps give distinct dagger functors, as their object maps differ. -/
theorem u_map_injective (m n : DaggerModels.ReverseSimplex) :
    Function.Injective (u.map : (m ⟶ n) → (u.obj m ⟶ u.obj n)) := by
  intro f g h
  apply DaggerModels.ReverseSimplex.Hom.ext
  intro i
  let a : FreeDaggerSimplex m.len := ⟨⟨i.val, i.isLt⟩⟩
  have hobj := congrArg (fun φ : u.obj m ⟶ u.obj n => φ.toFunctor.obj a) h
  apply Fin.ext
  exact congrArg (fun X : FreeDaggerSimplex n.len => X.vertex.val) hobj

instance u_faithful : u.Faithful where
  map_injective := by
    intro X Y f g h
    exact u_map_injective X Y h

/-- The image of a positive generator under a monotone map is its forward word. -/
theorem u_map_generator_monotone {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (hf : Monotone f.toFun) (a : ℕ) (ha : a + 1 ≤ m.len) :
    (u.map f).toFunctor.map (forwardEdge m.len a ha) =
      forwardWord n.len
        (mapLine f (lineAt m.len a (by omega))).val
        (mapLine f (lineAt m.len (a + 1) ha)).val
        (Nat.lt_succ_iff.mp (mapLine f (lineAt m.len a (by omega))).isLt)
        (Nat.lt_succ_iff.mp (mapLine f (lineAt m.len (a + 1) ha)).isLt)
        (mapLine_mono f hf (by simp only [lineAt_val]; omega)) := by
  change mapPath f (forwardEdge m.len a ha) = _
  rw [mapPath_forwardEdge, intervalWord_forward]

/-- The image of a positive generator under an antitone map is the daggered forward word. -/
theorem u_map_generator_antitone {m n : DaggerModels.ReverseSimplex}
    (f : m ⟶ n) (hf : Antitone f.toFun) (a : ℕ) (ha : a + 1 ≤ m.len) :
    (u.map f).toFunctor.map (forwardEdge m.len a ha) =
      DaggerModels.dagger (forwardWord n.len
        (mapLine f (lineAt m.len (a + 1) ha)).val
        (mapLine f (lineAt m.len a (by omega))).val
        (Nat.lt_succ_iff.mp (mapLine f (lineAt m.len (a + 1) ha)).isLt)
        (Nat.lt_succ_iff.mp (mapLine f (lineAt m.len a (by omega))).isLt)
        (mapLine_anti f hf (by simp only [lineAt_val]; omega))) := by
  change mapPath f (forwardEdge m.len a ha) = _
  rw [mapPath_forwardEdge, intervalWord_backward_le]

end DaggerModelsPartII.DaggerSimplexIndex
