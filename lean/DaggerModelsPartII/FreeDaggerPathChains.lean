import DaggerModelsPartII.DaggerNerveLengthFiltration
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Letter chains of arbitrary paths in a free dagger simplex

A path in the doubled line quiver is an unreduced word. Its letter chain
retains every edge, including neighboring mutually reverse edges.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerNerveLengthFiltration

namespace DaggerModels.PartII.FreeDaggerPathChains

noncomputable section

/-- A chain whose adjacent arrows are exactly the letters of a specified path. -/
structure LetterChainData (n : ℕ) {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) where
  chain : Fin (n + 1) ⥤ FreeDaggerSimplex m
  start : chain.obj 0 = a
  finish : chain.obj (Fin.last n) = b
  composite :
    eqToHom start.symm ≫
      chain.map (homOfLE (Fin.zero_le (Fin.last n))) ≫
        eqToHom finish = p
  adjacent (i : Fin n) :
    letterLength (chain.map (homOfLE (Fin.castSucc_le_succ i))) = 1

private theorem precomp_hom {m n : ℕ} (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    {a : FreeDaggerSimplex m} (f : a ⟶ F.obj 0) :
    (ComposableArrows.precomp F f).map
        (homOfLE (Fin.zero_le (Fin.last (n + 1)))) =
      f ≫ F.map (homOfLE (Fin.zero_le (Fin.last n))) := by
  cases n with
  | zero => simp [ComposableArrows.precomp, ComposableArrows.Precomp.map]
  | succ n => rfl

private theorem letterLength_eqToHom {m : ℕ} {a b : FreeDaggerSimplex m}
    (h : a = b) : letterLength (eqToHom h) = 0 := by
  cases h
  rfl

private theorem path_vertices_of_length_one {m : ℕ}
    {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : letterLength p = 1) :
    Quiver.Path.vertices p = [a.vertex, b.vertex] := by
  letI : Quiver (Line m) := symmLineQuiver m
  change Quiver.Path.length p = 0 + 1 at hp
  obtain ⟨c, e, q, hq, heq⟩ :=
    Quiver.Path.eq_toPath_comp_of_length_eq_succ p hp
  have hcb : c = b.vertex := Quiver.Path.eq_of_length_zero q hq
  subst c
  have hnil : q = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero q hq
  subst q
  simpa only [Quiver.Path.comp_nil, Quiver.Path.vertices_toPath] using
    congrArg Quiver.Path.vertices heq

private theorem path_toList_of_length_one {m : ℕ}
    {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : letterLength p = 1) : Quiver.Path.toList p = [a.vertex] := by
  letI : Quiver (Line m) := symmLineQuiver m
  change Quiver.Path.length p = 0 + 1 at hp
  obtain ⟨c, e, q, hq, heq⟩ :=
    Quiver.Path.eq_toPath_comp_of_length_eq_succ p hp
  have hcb : c = b.vertex := Quiver.Path.eq_of_length_zero q hq
  subst c
  have hnil : q = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero q hq
  subst q
  simpa [Quiver.Hom.toPath, Quiver.Path.toList] using
    congrArg Quiver.Path.toList heq

private theorem symmLine_hom_unique (m : ℕ)
    (x y : Quiver.Symmetrify (Line m))
    (f g : (symmLineQuiver m).Hom x y) : f = g := by
  change (PLift (x.val + 1 = y.val) ⊕ PLift (y.val + 1 = x.val)) at f g
  cases f with
  | inl hf =>
      cases g with
      | inl hg => congr 1; exact Subsingleton.elim _ _
      | inr hg =>
          have h₁ : x.val + 1 = y.val := hf.down
          have h₂ : y.val + 1 = x.val := hg.down
          omega
  | inr hf =>
      cases g with
      | inl hg =>
          have h₁ : y.val + 1 = x.val := hf.down
          have h₂ : x.val + 1 = y.val := hg.down
          omega
      | inr hg => congr 1; exact Subsingleton.elim _ _

private theorem path_eq_of_length_one {m : ℕ}
    {a b : FreeDaggerSimplex m} (p q : a ⟶ b)
    (hp : letterLength p = 1) (hq : letterLength q = 1) : p = q := by
  letI : Quiver (Line m) := symmLineQuiver m
  letI : ∀ x y : Quiver.Symmetrify (Line m),
      Subsingleton (x ⟶ y) := fun x y =>
    ⟨symmLine_hom_unique m x y⟩
  exact Quiver.Path.toList_injective a.vertex
    b.vertex (by rw [path_toList_of_length_one p hp,
      path_toList_of_length_one q hq])

private theorem exists_letterChainData (m : ℕ) :
    ∀ n, ∀ {a b : FreeDaggerSimplex m} (p : a ⟶ b),
      letterLength p = n → Nonempty (LetterChainData n p) := by
  letI : Quiver (Line m) := symmLineQuiver m
  intro n
  induction n with
  | zero =>
      intro a b p hp
      change Quiver.Path.length p = 0 at hp
      have hv : a.vertex = b.vertex := Quiver.Path.eq_of_length_zero p hp
      have hab : a = b := by
        cases a with | mk av =>
          cases b with | mk bv =>
            congr
      subst b
      have hnil : p = 𝟙 a := Quiver.Path.eq_nil_of_length_zero p hp
      subst p
      refine ⟨⟨ComposableArrows.mk₀ a, rfl, rfl, ?_, ?_⟩⟩
      · simp [ComposableArrows.mk₀]
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro a b p hp
      change Quiver.Path.length p = n + 1 at hp
      obtain ⟨c, e, q, hlen, hpath⟩ :=
        Quiver.Path.eq_toPath_comp_of_length_eq_succ p hp
      let cObj : FreeDaggerSimplex m := ⟨c⟩
      let q' : cObj ⟶ b := q
      obtain ⟨D⟩ := ih q' hlen
      let f : a ⟶ D.chain.obj 0 :=
        (e.toPath : a ⟶ cObj) ≫ eqToHom D.start.symm
      let G : Fin (n + 1 + 1) ⥤ FreeDaggerSimplex m :=
        ComposableArrows.precomp D.chain f
      refine ⟨⟨G, rfl, ?_, ?_, ?_⟩⟩
      · exact D.finish
      · calc
          eqToHom (rfl : G.obj 0 = a).symm ≫
              G.map (homOfLE (Fin.zero_le (Fin.last (n + 1)))) ≫
                eqToHom D.finish =
              (e.toPath : a ⟶ cObj) ≫
                (eqToHom D.start.symm ≫
                  D.chain.map (homOfLE (Fin.zero_le (Fin.last n))) ≫
                    eqToHom D.finish) := by
                rw [precomp_hom]
                simp only [eqToHom_refl, Category.id_comp, f, Category.assoc]
          _ = (e.toPath : a ⟶ cObj) ≫ q' := by rw [D.composite]
          _ = p := hpath.symm
      · intro i
        induction i using Fin.cases with
        | zero =>
            change letterLength f = 1
            change letterLength ((e.toPath : a ⟶ cObj) ≫
              eqToHom D.start.symm) = 1
            rw [letterLength_comp, letterLength_eqToHom]
            rfl
        | succ j =>
            simpa only [G, ComposableArrows.precomp,
              ComposableArrows.Precomp.map_succ_succ] using D.adjacent j

/-- A fully witnessed letter chain of an arbitrary unreduced path. -/
private def chosenLetterChainData {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) : LetterChainData (letterLength p) p :=
  (exists_letterChainData m (letterLength p) p rfl).some

/-- The chain of individual letters of any unreduced free dagger path. -/
def letterChain {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b) :
    Fin (letterLength p + 1) ⥤ FreeDaggerSimplex m :=
  (chosenLetterChainData p).chain

/-- The first object of the letter chain is the source of the path. -/
theorem letterChain_start {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b) :
    (letterChain p).obj 0 = a :=
  (chosenLetterChainData p).start

/-- The last object of the letter chain is the target of the path. -/
theorem letterChain_finish {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b) :
    (letterChain p).obj (Fin.last (letterLength p)) = b :=
  (chosenLetterChainData p).finish

/-- Composing every letter of the chain recovers the given unreduced path. -/
theorem letterChain_composite {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) :
    eqToHom (letterChain_start p).symm ≫
      (letterChain p).map
        (homOfLE (Fin.zero_le (Fin.last (letterLength p)))) ≫
        eqToHom (letterChain_finish p) = p :=
  (chosenLetterChainData p).composite

/-- Each adjacent arrow of the letter chain has exactly one letter. -/
theorem letterChain_adjacent_length {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) (i : Fin (letterLength p)) :
    letterLength ((letterChain p).map
      (homOfLE (Fin.castSucc_le_succ i))) = 1 :=
  (chosenLetterChainData p).adjacent i

private theorem chain_vertices (m : ℕ) : ∀ (n : ℕ)
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m),
    (∀ i : Fin n,
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1) →
    Quiver.Path.vertices
      (F.map (homOfLE (Fin.zero_le (Fin.last n)))) =
        List.ofFn (fun i : Fin (n + 1) => (F.obj i).vertex) := by
  intro n
  induction n with
  | zero =>
      intro F _
      have hid : F.map (homOfLE (Fin.zero_le (Fin.last 0))) = 𝟙 (F.obj 0) := by
        simp
      rw [hid]
      rfl

  | succ n ih =>
      intro F h
      let I : Fin (n + 1) ⥤ FreeDaggerSimplex m := initialChain F
      have hI : ∀ i : Fin n,
          letterLength (I.map (homOfLE (Fin.castSucc_le_succ i))) = 1 := by
        intro i
        exact h i.castSucc
      let e := F.map (homOfLE (Fin.castSucc_le_succ (Fin.last n)))
      have he : letterLength e = 1 := h (Fin.last n)
      have hcomp :
          F.map (homOfLE (Fin.zero_le (Fin.last (n + 1)))) =
            I.map (homOfLE (Fin.zero_le (Fin.last n))) ≫ e := by
        change F.map (homOfLE (Fin.zero_le (Fin.last (n + 1)))) =
          F.map (homOfLE (Fin.zero_le (Fin.last n).castSucc)) ≫
            F.map (homOfLE (Fin.castSucc_le_succ (Fin.last n)))
        rw [← F.map_comp]
        congr 1
      rw [hcomp]
      change Quiver.Path.vertices
        ((I.map (homOfLE (Fin.zero_le (Fin.last n)))).comp e) = _
      rw [Quiver.Path.vertices_comp, ih I hI,
        path_vertices_of_length_one e he]
      simp only [List.ofFn_succ', List.dropLast_concat,
        List.concat_eq_append, List.append_assoc, List.singleton_append]
      rfl

private theorem path_vertices_eqToHom_comp {m : ℕ}
    {a a' b b' : FreeDaggerSimplex m} (hs : a' = a) (ht : b' = b)
    (q : a' ⟶ b') :
    Quiver.Path.vertices (eqToHom hs.symm ≫ q ≫ eqToHom ht) =
      Quiver.Path.vertices q := by
  cases hs
  cases ht
  simp

private theorem eqToHom_comp_of_heq {m : ℕ}
    {a b c d : FreeDaggerSimplex m} (p : a ⟶ b) (q : c ⟶ d)
    (ha : a = c) (hb : b = d) (hp : p ≍ q) :
    eqToHom ha.symm ≫ p ≫ eqToHom hb = q := by
  cases ha
  cases hb
  simpa using eq_of_heq hp

private theorem dagger_eqToHom {m : ℕ} {a b : FreeDaggerSimplex m}
    (h : a = b) : dagger (eqToHom h) = eqToHom h.symm := by
  cases h
  simp

private theorem eqToHom_transport_trans {m : ℕ}
    {c d u v b a : FreeDaggerSimplex m} (f : c ⟶ d)
    (hcu : c = u) (hdv : d = v) (hub : u = b) (hva : v = a) :
    eqToHom (hcu.trans hub).symm ≫ f ≫
        eqToHom (hdv.trans hva) =
      eqToHom hub.symm ≫ (eqToHom hcu.symm ≫ f ≫ eqToHom hdv) ≫
        eqToHom hva := by
  cases hcu
  cases hdv
  cases hub
  cases hva
  simp

/-- An unreduced path has a unique chain with one letter on each adjacent edge. -/
theorem letterChainData_unique {m n : ℕ} {a b : FreeDaggerSimplex m}
    {p : a ⟶ b} (D E : LetterChainData n p) : D.chain = E.chain := by
  have hD : Quiver.Path.vertices
      (D.chain.map (homOfLE (Fin.zero_le (Fin.last n)))) =
      Quiver.Path.vertices p := by
    have hc := congrArg Quiver.Path.vertices D.composite
    exact (path_vertices_eqToHom_comp D.start D.finish _).symm.trans hc
  have hE : Quiver.Path.vertices
      (E.chain.map (homOfLE (Fin.zero_le (Fin.last n)))) =
      Quiver.Path.vertices p := by
    have hc := congrArg Quiver.Path.vertices E.composite
    exact (path_vertices_eqToHom_comp E.start E.finish _).symm.trans hc
  have hlist :
      List.ofFn (fun i : Fin (n + 1) => (D.chain.obj i).vertex) =
      List.ofFn (fun i : Fin (n + 1) => (E.chain.obj i).vertex) := by
    calc
      _ = Quiver.Path.vertices
          (D.chain.map (homOfLE (Fin.zero_le (Fin.last n)))) :=
        (chain_vertices m n D.chain D.adjacent).symm
      _ = Quiver.Path.vertices p := hD
      _ = Quiver.Path.vertices
          (E.chain.map (homOfLE (Fin.zero_le (Fin.last n)))) := hE.symm
      _ = _ := chain_vertices m n E.chain E.adjacent
  have hobj : ∀ i : Fin (n + 1), D.chain.obj i = E.chain.obj i := by
    intro i
    have hv := congrFun (List.ofFn_injective hlist) i
    cases hx : D.chain.obj i with | mk x =>
      cases hy : E.chain.obj i with | mk y =>
        simpa only [hx, hy] using congrArg FreeDaggerSimplex.mk hv
  apply ComposableArrows.ext hobj
  intro i hi
  have hd : letterLength (ComposableArrows.map' D.chain i (i + 1)) = 1 :=
    D.adjacent ⟨i, hi⟩
  have he : letterLength (ComposableArrows.map' E.chain i (i + 1)) = 1 :=
    E.adjacent ⟨i, hi⟩
  have ht : letterLength
      (eqToHom (hobj ⟨i, by omega⟩) ≫
        ComposableArrows.map' E.chain i (i + 1) ≫
        eqToHom (hobj ⟨i + 1, by omega⟩).symm) = 1 := by
    rw [letterLength_comp, letterLength_comp,
      letterLength_eqToHom, letterLength_eqToHom]
    simpa using he
  exact path_eq_of_length_one _ _ hd ht

private theorem letterChainData_chain_cast {m n n' : ℕ}
    {a b : FreeDaggerSimplex m} {p : a ⟶ b}
    (h : n = n') (D : LetterChainData n p) :
    (h ▸ D).chain = h ▸ D.chain := by
  cases h
  rfl

private theorem reverse_chain_map_heq (n m : ℕ)
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap
        (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) F).map
      (homOfLE h) ≍
      dagger (F.map (homOfLE (Fin.rev_le_rev.mpr h))) := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have ha : Antitone (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)).toFun := by
    intro x y hxy
    simpa only [ReverseSimplex.reversal_apply, Fin.rev_le_rev] using hxy
  have hid : ReverseSimplex.antitoneHom
      (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) ha = 𝟙 ⦋n⦌ := by
    ext x
    simp [ReverseSimplex.antitoneHom]
  rw [X.extensionMap_antitone _ ha, hid, op_id, X.toSSet.map_id]
  change (SSet.opObjEquiv
    ((DaggerNativeOrdinaryDaggerNerve.reversal (FreeDaggerSimplex m)).app
      (op ⦋n⦌) F)).map (homOfLE h) ≍ _
  rw [DaggerNativeOrdinaryDaggerNerve.reversal_map]
  simp [DaggerOriginalNerveOppositeMap.reverseDiagram,
    ComposableArrows.opEquivalence, Fin.revOrderIso]
  congr 1

/-- Reversal of any interval arrow is the dagger of the opposite interval arrow.
The heterogeneous equality retains the actual endpoints of both chains. -/
theorem reversal_chain_map_heq (n m : ℕ)
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap
        (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) F).map
      (homOfLE h) ≍
      dagger (F.map (homOfLE (Fin.rev_le_rev.mpr h))) :=
  reverse_chain_map_heq n m F h

private theorem reversal_chain_obj (n m : ℕ)
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    (i : Fin (n + 1)) :
    ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap
        (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) F).obj i =
      F.obj i.rev := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have ha : Antitone (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)).toFun := by
    intro x y hxy
    simpa only [ReverseSimplex.reversal_apply, Fin.rev_le_rev] using hxy
  have hid : ReverseSimplex.antitoneHom
      (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) ha = 𝟙 ⦋n⦌ := by
    ext x
    simp [ReverseSimplex.antitoneHom]
  rw [X.extensionMap_antitone _ ha, hid, op_id, X.toSSet.map_id]
  exact DaggerNativeOrdinaryDaggerNerve.reversal_obj
    (FreeDaggerSimplex m) ⦋n⦌ F i

/-- Reversal preserves the chain objects in the opposite order. -/
theorem reversal_chain_object (n m : ℕ)
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    (i : Fin (n + 1)) :
    ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap
        (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) F).obj i =
      F.obj i.rev :=
  reversal_chain_obj n m F i

private theorem reversal_chain_length (n m : ℕ)
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    letterLength
      (((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap
          (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) F).map
        (homOfLE h)) =
      letterLength (F.map (homOfLE (Fin.rev_le_rev.mpr h))) := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have ha : Antitone (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)).toFun := by
    intro x y hxy
    simpa only [ReverseSimplex.reversal_apply, Fin.rev_le_rev] using hxy
  have hid : ReverseSimplex.antitoneHom
      (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) ha = 𝟙 ⦋n⦌ := by
    ext x
    simp [ReverseSimplex.antitoneHom]
  rw [X.extensionMap_antitone _ ha, hid, op_id, X.toSSet.map_id]
  change letterLength ((SSet.opObjEquiv
    ((DaggerNativeOrdinaryDaggerNerve.reversal (FreeDaggerSimplex m)).app
      (op ⦋n⦌) F)).map (homOfLE h)) = _
  rw [DaggerNativeOrdinaryDaggerNerve.reversal_map]
  simp [DaggerOriginalNerveOppositeMap.reverseDiagram,
    ComposableArrows.opEquivalence, Fin.revOrderIso]
  rw [letterLength_dagger]
  congr 1

private def reversedLetterChainData {m n : ℕ}
    {a b : FreeDaggerSimplex m} {p : a ⟶ b}
    (D : LetterChainData n p) : LetterChainData n (dagger p) := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  let R : Fin (n + 1) ⥤ FreeDaggerSimplex m :=
    X.extensionMap (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) D.chain
  have hRstart : R.obj 0 = D.chain.obj (Fin.last n) := by
    simpa only [Fin.rev_zero] using reversal_chain_object n m D.chain 0
  have hRfinish : R.obj (Fin.last n) = D.chain.obj 0 := by
    simpa only [Fin.rev_last] using
      reversal_chain_object n m D.chain (Fin.last n)
  let hs : R.obj 0 = b := hRstart.trans D.finish
  let ht : R.obj (Fin.last n) = a := hRfinish.trans D.start
  refine ⟨R, hs, ht, ?_, ?_⟩
  · have hrev :
        eqToHom hRstart.symm ≫
          R.map (homOfLE (Fin.zero_le (Fin.last n))) ≫
            eqToHom hRfinish =
          dagger (D.chain.map (homOfLE (Fin.zero_le (Fin.last n)))) := by
      have hh := reversal_chain_map_heq n m D.chain
        (Fin.zero_le (Fin.last n))
      change R.map (homOfLE (Fin.zero_le (Fin.last n))) ≍
        dagger (D.chain.map (homOfLE (Fin.rev_le_rev.mpr
          (Fin.zero_le (Fin.last n))))) at hh
      have hh' : R.map (homOfLE (Fin.zero_le (Fin.last n))) ≍
          dagger (D.chain.map (homOfLE (Fin.zero_le (Fin.last n)))) := by
        convert hh using 1
        · simp only [Fin.rev_zero, Fin.rev_last]
        · congr 1
          · exact congrArg D.chain.obj (Fin.rev_last n).symm
          · apply freeChain_map_heq D.chain
            · exact (Fin.rev_last n).symm
            · exact (Fin.rev_zero n).symm
      exact eqToHom_comp_of_heq _ _ hRstart hRfinish hh'
    calc
      eqToHom hs.symm ≫ R.map (homOfLE (Fin.zero_le (Fin.last n))) ≫
          eqToHom ht =
          eqToHom D.finish.symm ≫
            (eqToHom hRstart.symm ≫
              R.map (homOfLE (Fin.zero_le (Fin.last n))) ≫
                eqToHom hRfinish) ≫
              eqToHom D.start :=
          eqToHom_transport_trans _ hRstart hRfinish D.finish D.start
      _ = eqToHom D.finish.symm ≫
            dagger (D.chain.map (homOfLE (Fin.zero_le (Fin.last n)))) ≫
              eqToHom D.start := by rw [hrev]
      _ = dagger p := by
        have hd := congrArg dagger D.composite
        rw [DaggerCategory.dagger_comp, DaggerCategory.dagger_comp,
          dagger_eqToHom, dagger_eqToHom] at hd
        simpa only [Category.assoc] using hd
  · intro i
    have hlen := reversal_chain_length n m D.chain
      (Fin.castSucc_le_succ i)
    have hlen' :
        letterLength (D.chain.map
          (homOfLE (Fin.rev_le_rev.mpr (Fin.castSucc_le_succ i)))) = 1 := by
      convert D.adjacent i.rev using 1
      congr 1
      · exact congrArg D.chain.obj (Fin.rev_succ i)
      · exact congrArg D.chain.obj (Fin.rev_castSucc i)
      · apply freeChain_map_heq D.chain
        · exact Fin.rev_succ i
        · exact Fin.rev_castSucc i
    exact hlen.trans hlen'

/-- The native reversal of a letter chain is the letter chain of the dagger path. -/
theorem letterChain_dagger {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) :
    (letterLength_dagger p) ▸ letterChain (dagger p) =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap
          (ReverseSimplex.reversal
            (⟨letterLength p⟩ : ReverseSimplex)) (letterChain p) := by
  have h := letterChainData_unique
    ((letterLength_dagger p) ▸ chosenLetterChainData (dagger p))
    (reversedLetterChainData (chosenLetterChainData p))
  rw [letterChainData_chain_cast] at h
  exact h


/-- The total length of the letter chain is the actual length of the path. -/
theorem totalLength_letterChain {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) :
    totalLength (letterLength p) m (letterChain p) = letterLength p := by
  rw [totalLength_eq_composite]
  have h := congrArg letterLength (letterChain_composite p)
  simpa only [letterLength_comp, letterLength_eqToHom,
    zero_add, add_zero] using h

/-- The Yoneda classifying map of the letter chain in the native dagger nerve. -/
def characteristic {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b) :
    yoneda.obj (⟨letterLength p⟩ : ReverseSimplex) ⟶
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extension :=
  yonedaEquiv.symm (letterChain p)

/-- The characteristic map evaluates by pulling back the letter chain. -/
theorem characteristic_app {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    {k : ReverseSimplex} (φ : k ⟶ ⟨letterLength p⟩) :
    (characteristic p).app (op k) φ =
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extension.map φ.op) (letterChain p) := by
  exact yonedaEquiv_symm_app_apply
    (F := (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extension) (letterChain p) (op k) φ

private theorem yonedaEquiv_symm_cast (m : ℕ) {n n' : ℕ}
    (h : n = n') (F : Fin (n + 1) ⥤ FreeDaggerSimplex m) :
    h ▸ (yonedaEquiv.symm F :
      yoneda.obj (⟨n⟩ : ReverseSimplex) ⟶
        (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extension) =
      yonedaEquiv.symm (h ▸ F) := by
  cases h
  rfl

/-- The characteristic map of the dagger word is the target-reversal flip of
the characteristic map of the original unreduced word. -/
theorem characteristic_dagger {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) :
    (letterLength_dagger p) ▸ characteristic (dagger p) =
      yoneda.map (ReverseSimplex.reversal
        (⟨letterLength p⟩ : ReverseSimplex)) ≫ characteristic p := by
  change (letterLength_dagger p) ▸
      (yonedaEquiv.symm (letterChain (dagger p)) :
        yoneda.obj (⟨letterLength (dagger p)⟩ : ReverseSimplex) ⟶
          (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
            (FreeDaggerSimplex m)).extension) =
    yoneda.map (ReverseSimplex.reversal
      (⟨letterLength p⟩ : ReverseSimplex)) ≫
        yonedaEquiv.symm (letterChain p)
  rw [yonedaEquiv_symm_cast]
  rw [yonedaEquiv_symm_naturality_left]
  exact congrArg yonedaEquiv.symm (letterChain_dagger p)

end

end DaggerModels.PartII.FreeDaggerPathChains
