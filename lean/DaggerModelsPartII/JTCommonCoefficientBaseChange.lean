import DaggerModelsPartII.JTCommonCoefficientLiftChoices

/-!
# Base change of a common coefficient without merging source images
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)

noncomputable section

variable {k b b' n m l : SimplexCategory}

private theorem image_le_iff (c : k ⟶ b) (v : b ⟶ b')
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a')
    (a a' : Fin (k.len + 1)) :
    v.toOrderHom (c.toOrderHom a) ≤ v.toOrderHom (c.toOrderHom a') ↔
      c.toOrderHom a ≤ c.toOrderHom a' := by
  constructor
  · intro h
    by_cases hc : c.toOrderHom a ≤ c.toOrderHom a'
    · exact hc
    · have hr : c.toOrderHom a' ≤ c.toOrderHom a := le_of_not_ge hc
      have he : v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') :=
        le_antisymm h (v.toOrderHom.monotone hr)
      exact hc.elim (le_of_eq (H a a' he))
  · intro h
    exact v.toOrderHom.monotone h

private theorem vertex_order_iff (c : k ⟶ b) (v : b ⟶ b')
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a')
    (x y : Fin (k.len + 1) × Fin (n.len + 1)) :
    vertexEquiv (c ≫ v) n x ≤ vertexEquiv (c ≫ v) n y ↔
      vertexEquiv c n x ≤ vertexEquiv c n y := by
  rw [vertex_le_iff, vertex_le_iff]
  change (v.toOrderHom (c.toOrderHom x.1) ≤ v.toOrderHom (c.toOrderHom y.1) ∧
    (v.toOrderHom (c.toOrderHom x.1) = v.toOrderHom (c.toOrderHom y.1) →
      x.2 ≤ y.2 ∧ (x.2 = y.2 → x.1 ≤ y.1))) ↔ _
  rw [image_le_iff c v H x.1 y.1]
  have he : v.toOrderHom (c.toOrderHom x.1) = v.toOrderHom (c.toOrderHom y.1) ↔
      c.toOrderHom x.1 = c.toOrderHom y.1 :=
    ⟨H x.1 y.1, fun h ↦ congrArg v.toOrderHom h⟩
  simp only [he]

/-- An operator that is injective on the image of `c` does not change the vertex ranks. -/
theorem vertexEquiv_comp_eq (c : k ⟶ b) (v : b ⟶ b')
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a') (n : SimplexCategory) :
    vertexEquiv (c ≫ v) n = vertexEquiv c n := by
  let e : Fin ((common k n).len + 1) ≃o Fin ((common k n).len + 1) :=
    { toEquiv := (vertexEquiv c n).symm.trans (vertexEquiv (c ≫ v) n)
      map_rel_iff' := by
        intro x y
        simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
          (vertex_order_iff c v H
            ((vertexEquiv c n).symm x) ((vertexEquiv c n).symm y)) }
  apply Equiv.ext
  intro x
  have h := Fin.coe_orderIso_apply e (vertexEquiv c n x)
  have he : e (vertexEquiv c n x) = vertexEquiv c n x := Fin.ext h
  simpa [e] using he

/-- The enlarged simplex has exactly the expected base after coefficient base change. -/
theorem base_comp_eq (c : k ⟶ b) (v : b ⟶ b')
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a') (n : SimplexCategory) :
    base (c ≫ v) n = base c n ≫ v := by
  ext z : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective z
  change (base (c ≫ v) n).toOrderHom (vertexEquiv c n x) =
    v.toOrderHom ((base c n).toOrderHom (vertexEquiv c n x))
  rw [← vertexEquiv_comp_eq c v H n, base_vertexEquiv]
  rw [vertexEquiv_comp_eq c v H n, base_vertexEquiv]
  rfl

/-- The prism embedding is unchanged when the source image stays distinct. -/
theorem prism_comp_eq (c : k ⟶ b) (v : b ⟶ b')
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a') (n : SimplexCategory) :
    prism.{u} (c ≫ v) n = prism c n := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      apply NatTrans.ext
      funext q x
      induction q using Opposite.rec with | op q =>
        induction q using SimplexCategory.rec with | h d =>
          apply SSet.stdSimplex.objEquiv.injective
          ext a : 3
          change vertexEquiv (c ≫ v) ⦋n⦌ (SSet.prodStdSimplex.objEquiv x a) =
            vertexEquiv c ⦋n⦌ (SSet.prodStdSimplex.objEquiv x a)
          rw [vertexEquiv_comp_eq c v H ⦋n⦌]

/-- Every fixed-time slice uses the same vertices after coefficient base change. -/
theorem slice_comp_eq (c : k ⟶ b) (v : b ⟶ b')
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a')
    (n : SimplexCategory) (t : Fin (n.len + 1)) :
    slice (c ≫ v) n t = slice c n t := by
  ext a : 3
  exact congrArg (fun e ↦ e (a, t)) (vertexEquiv_comp_eq c v H n)

/-- Every vertical section uses the same vertices after coefficient base change. -/
theorem vertical_comp_eq (c : k ⟶ b) (v : b ⟶ b')
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a')
    (n : SimplexCategory) (a : Fin (k.len + 1)) :
    vertical (c ≫ v) n a = vertical c n a := by
  ext t : 3
  exact congrArg (fun e ↦ e (a, t)) (vertexEquiv_comp_eq c v H n)

/-- The reindexing map depends only on the vertex ranks of its two endpoints. -/
theorem map_eq_of_vertexEquiv_eq
    {c : k ⟶ b} {d : l ⟶ b} {c' : k ⟶ b'} {d' : l ⟶ b'}
    (f : k ⟶ l) (hf : f ≫ d = c) (hf' : f ≫ d' = c')
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (hc : vertexEquiv c n = vertexEquiv c' n)
    (hd : vertexEquiv d m = vertexEquiv d' m) :
    map f hf j hj = map f hf' j hj := by
  ext z : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective z
  rw [map_vertexEquiv]
  rw [hc, map_vertexEquiv, ← hd]

/-- Base change commutes exactly with reindexing when both images are preserved. -/
theorem map_comp_eq
    {c : k ⟶ b} {d : l ⟶ b}
    (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (v : b ⟶ b')
    (Hc : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a')
    (Hd : ∀ a a' : Fin (l.len + 1),
      v.toOrderHom (d.toOrderHom a) = v.toOrderHom (d.toOrderHom a') →
        d.toOrderHom a = d.toOrderHom a') :
    map f hf j hj = map f (show f ≫ (d ≫ v) = c ≫ v by rw [← Category.assoc, hf])
      j hj := by
  exact map_eq_of_vertexEquiv_eq f hf _ j hj
    (vertexEquiv_comp_eq c v Hc n).symm
    (vertexEquiv_comp_eq d v Hd m).symm

end

end DaggerModels.PartII.JTCommonCoefficientParameter

namespace DaggerModels.PartII.JTCommonCoefficientLiftChoices

open JTCommonCoefficientParameter

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{u}.obj a

variable {A X Y : SSet.{u}} {k b b' n : SimplexCategory}
variable {c : k ⟶ b} {v : b ⟶ b'}
variable {g : simplex b' ⟶ Y} {t : A ⟶ X} {p : X ⟶ Y}
variable {i : A ⟶ simplex k}

/-- A stationary extension retains its enlarged map after a coefficient base change
that keeps the image of the source vertices distinct. -/
def transportBaseChange
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a')
    (sq : CommSq t i p (SSet.stdSimplex.map c ≫ (SSet.stdSimplex.map v ≫ g)))
    (sq' : CommSq t i p (SSet.stdSimplex.map (c ≫ v) ≫ g))
    (E : Extension sq n) : Extension sq' n where
  map := E.map
  stationary := by
    rw [prism_comp_eq c v H n]
    exact E.stationary
  over := by
    rw [base_comp_eq c v H n, SSet.stdSimplex.map_comp, Category.assoc]
    exact E.over

theorem transportBaseChange_map
    (H : ∀ a a' : Fin (k.len + 1),
      v.toOrderHom (c.toOrderHom a) = v.toOrderHom (c.toOrderHom a') →
        c.toOrderHom a = c.toOrderHom a')
    (sq : CommSq t i p (SSet.stdSimplex.map c ≫ (SSet.stdSimplex.map v ≫ g)))
    (sq' : CommSq t i p (SSet.stdSimplex.map (c ≫ v) ≫ g))
    (E : Extension sq n) :
    (transportBaseChange H sq sq' E).map = E.map := rfl

end

end DaggerModels.PartII.JTCommonCoefficientLiftChoices
