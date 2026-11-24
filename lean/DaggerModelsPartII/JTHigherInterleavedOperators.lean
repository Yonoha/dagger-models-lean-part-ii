import DaggerModelsPartII.JTHigherInterleavedParameter

/-!
# Time operators on higher interleaved parameters

Time operators preserve the original coordinate and act on the time
coordinate by the actual simplex operator.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory

universe u

namespace DaggerModels.PartII.JTHigherInterleavedParameter

private theorem vertexEquiv_lt_of_fst_lt (k n : SimplexCategory)
    {x y : Fin (k.len + 1) × Fin (n.len + 1)} (h : x.1 < y.1) :
    vertexEquiv k n x < vertexEquiv k n y := by
  change (vertexEquiv k n x).val < (vertexEquiv k n y).val
  simp only [vertexEquiv_val]
  calc
    x.2.val + (n.len + 1) * x.1.val <
        (n.len + 1) * (x.1.val + 1) := by
      rw [Nat.mul_succ]
      have ht := x.2.isLt
      omega
    _ ≤ (n.len + 1) * y.1.val := Nat.mul_le_mul_left _ h
    _ ≤ y.2.val + (n.len + 1) * y.1.val := Nat.le_add_left _ _

private theorem mapTime_mono {k n m : SimplexCategory} (f : n ⟶ m) :
    Monotone (fun v ↦
      let x := (vertexEquiv k n).symm v
      vertexEquiv k m (x.1, f.toOrderHom x.2)) := by
  intro v w h
  let x := (vertexEquiv k n).symm v
  let y := (vertexEquiv k n).symm w
  have hxy : vertexEquiv k n x ≤ vertexEquiv k n y := by
    simpa only [x, y, Equiv.apply_symm_apply] using h
  have hfst : x.1 ≤ y.1 := by
    by_contra! hfst
    exact (not_lt_of_ge hxy) (vertexEquiv_lt_of_fst_lt k n hfst)
  change vertexEquiv k m (x.1, f.toOrderHom x.2) ≤
    vertexEquiv k m (y.1, f.toOrderHom y.2)
  rcases lt_or_eq_of_le hfst with hlt | heq
  · exact (vertexEquiv_lt_of_fst_lt k m hlt).le
  · have hsnd : x.2 ≤ y.2 := by
      change (vertexEquiv k n x).val ≤ (vertexEquiv k n y).val at hxy
      simp only [vertexEquiv_val, heq] at hxy
      exact Nat.le_of_add_le_add_right hxy
    exact (prismOrder k m).monotone ⟨hfst, f.toOrderHom.monotone hsnd⟩

/-- Apply a simplex operator in the time coordinate of the ordered parameter. -/
def mapTime (k : SimplexCategory) {n m : SimplexCategory} (f : n ⟶ m) :
    common k n ⟶ common k m :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    let x := (vertexEquiv k n).symm v
    vertexEquiv k m (x.1, f.toOrderHom x.2), mapTime_mono f⟩

@[simp] theorem mapTime_vertexEquiv (k : SimplexCategory) {n m : SimplexCategory}
    (f : n ⟶ m) (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (mapTime k f).toOrderHom (vertexEquiv k n x) =
      vertexEquiv k m (x.1, f.toOrderHom x.2) := by
  change (let v := (vertexEquiv k n).symm (vertexEquiv k n x)
          vertexEquiv k m (v.1, f.toOrderHom v.2)) = _
  rw [Equiv.symm_apply_apply]

theorem mapTime_id (k n : SimplexCategory) :
    mapTime k (𝟙 n) = 𝟙 (common k n) := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv k n).surjective v
  rw [mapTime_vertexEquiv]
  rfl

theorem mapTime_comp (k : SimplexCategory) {n m l : SimplexCategory}
    (f : n ⟶ m) (g : m ⟶ l) :
    mapTime k (f ≫ g) = mapTime k f ≫ mapTime k g := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv k n).surjective v
  change (mapTime k (f ≫ g)).toOrderHom (vertexEquiv k n x) =
    (mapTime k g).toOrderHom ((mapTime k f).toOrderHom (vertexEquiv k n x))
  simp only [mapTime_vertexEquiv]
  rfl

theorem mapTime_ret (k : SimplexCategory) {n m : SimplexCategory} (f : n ⟶ m) :
    mapTime k f ≫ ret k m = ret k n := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv k n).surjective v
  change (ret k m).toOrderHom ((mapTime k f).toOrderHom (vertexEquiv k n x)) =
    (ret k n).toOrderHom (vertexEquiv k n x)
  simp only [mapTime_vertexEquiv, ret_vertexEquiv]

theorem slice_mapTime (k : SimplexCategory) {n m : SimplexCategory}
    (f : n ⟶ m) (t : Fin (n.len + 1)) :
    slice k n t ≫ mapTime k f = slice k m (f.toOrderHom t) := by
  ext a : 3
  exact mapTime_vertexEquiv k f (a, t)

theorem vertical_mapTime (k : SimplexCategory) {n m : SimplexCategory}
    (f : n ⟶ m) (a : Fin (k.len + 1)) :
    vertical k n a ≫ mapTime k f = f ≫ vertical k m a := by
  ext t : 3
  exact mapTime_vertexEquiv k f (a, t)

theorem prism_mapTime (k : SimplexCategory) {n m : SimplexCategory} (f : n ⟶ m) :
    prism.{u} k n ≫ SSet.stdSimplex.map (mapTime k f) =
      (SSet.stdSimplex.obj k ◁ SSet.stdSimplex.map f) ≫ prism k m := by
  induction k using SimplexCategory.rec with
  | _ k =>
    induction n using SimplexCategory.rec with
    | _ n =>
      induction m using SimplexCategory.rec with
      | _ m =>
        apply NatTrans.ext
        funext q x
        induction q using Opposite.rec with | op q =>
          induction q using SimplexCategory.rec with | h d =>
            apply SSet.stdSimplex.objEquiv.injective
            ext a : 3
            exact mapTime_vertexEquiv ⦋k⦌ f (SSet.prodStdSimplex.objEquiv x a)

end DaggerModels.PartII.JTHigherInterleavedParameter
