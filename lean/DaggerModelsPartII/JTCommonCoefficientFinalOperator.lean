import DaggerModelsPartII.JTCommonCoefficientPrism

/-!
# Comparison with the existing interleaving at the final coefficient
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

universe u

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)

noncomputable section

variable {k l b n m : SimplexCategory}

private theorem old_lt_of_base_lt (b n : SimplexCategory)
    (x y : Fin (b.len + 1) × Fin (n.len + 1)) (h : x.1 < y.1) :
    JTHigherInterleavedParameter.vertexEquiv b n x <
      JTHigherInterleavedParameter.vertexEquiv b n y := by
  change (JTHigherInterleavedParameter.vertexEquiv b n x).val <
    (JTHigherInterleavedParameter.vertexEquiv b n y).val
  simp only [JTHigherInterleavedParameter.vertexEquiv_val]
  calc
    x.2.val + (n.len + 1) * x.1.val < (n.len + 1) * (x.1.val + 1) := by
      rw [Nat.mul_succ]
      have := x.2.isLt
      omega
    _ ≤ (n.len + 1) * y.1.val := Nat.mul_le_mul_left _ h
    _ ≤ y.2.val + (n.len + 1) * y.1.val := Nat.le_add_left _ _

/-- Send the source vertex to its final coefficient and retain time,
using the existing order at the final coefficient. -/
def toFinal (c : k ⟶ b) (n : SimplexCategory) : common k n ⟶ common b n :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    let p := (vertexEquiv c n).symm v
    JTHigherInterleavedParameter.vertexEquiv b n (c.toOrderHom p.1, p.2), by
    intro v w h
    obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective v
    obtain ⟨y, rfl⟩ := (vertexEquiv c n).surjective w
    simp only [Equiv.symm_apply_apply]
    have hx := (vertex_le_iff c n x y).1 h
    rcases lt_or_eq_of_le hx.1 with hlt | heq
    · exact (old_lt_of_base_lt b n _ _ hlt).le
    · exact (JTHigherInterleavedParameter.prismOrder b n).monotone
        ⟨heq.le, (hx.2 heq).1⟩⟩

@[simp] theorem toFinal_vertexEquiv (c : k ⟶ b) (n : SimplexCategory)
    (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (toFinal c n).toOrderHom (vertexEquiv c n x) =
      JTHigherInterleavedParameter.vertexEquiv b n (c.toOrderHom x.1, x.2) := by
  change JTHigherInterleavedParameter.vertexEquiv b n
    (c.toOrderHom ((vertexEquiv c n).symm (vertexEquiv c n x)).1,
      ((vertexEquiv c n).symm (vertexEquiv c n x)).2) = _
  rw [Equiv.symm_apply_apply]

theorem toFinal_ret (c : k ⟶ b) (n : SimplexCategory) :
    toFinal c n ≫ JTHigherInterleavedParameter.ret b n = base c n := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective v
  change (JTHigherInterleavedParameter.ret b n).toOrderHom
    ((toFinal c n).toOrderHom (vertexEquiv c n x)) = _
  rw [toFinal_vertexEquiv, JTHigherInterleavedParameter.ret_vertexEquiv, base_vertexEquiv]

theorem slice_toFinal (c : k ⟶ b) (n : SimplexCategory) (t : Fin (n.len + 1)) :
    slice c n t ≫ toFinal c n = c ≫ JTHigherInterleavedParameter.slice b n t := by
  ext a : 3
  exact toFinal_vertexEquiv c n (a, t)

theorem vertical_toFinal (c : k ⟶ b) (n : SimplexCategory) (a : Fin (k.len + 1)) :
    vertical c n a ≫ toFinal c n =
      JTHigherInterleavedParameter.vertical b n (c.toOrderHom a) := by
  ext t : 3
  exact toFinal_vertexEquiv c n (a, t)

/-- Comparison with the existing order is natural along the original
coefficient operators and time embeddings. -/
theorem map_toFinal {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) :
    map f hf j hj ≫ toFinal d m =
      toFinal c n ≫ JTHigherInterleavedParameter.mapTime b j := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c n).surjective v
  change (toFinal d m).toOrderHom ((map f hf j hj).toOrderHom (vertexEquiv c n x)) =
    (JTHigherInterleavedParameter.mapTime b j).toOrderHom ((toFinal c n).toOrderHom (vertexEquiv c n x))
  rw [map_vertexEquiv, toFinal_vertexEquiv, toFinal_vertexEquiv,
    JTHigherInterleavedParameter.mapTime_vertexEquiv]
  have h := congrArg (fun z : k ⟶ b ↦ z.toOrderHom x.1) hf
  exact congrArg (fun a ↦ JTHigherInterleavedParameter.vertexEquiv b m (a, j.toOrderHom x.2)) h

theorem prism_toFinal (c : k ⟶ b) (n : SimplexCategory) :
    prism.{u} c n ≫ SSet.stdSimplex.map (toFinal c n) =
      (SSet.stdSimplex.map c ▷ SSet.stdSimplex.obj n) ≫ JTHigherInterleavedParameter.prism b n := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases b using SimplexCategory.rec with
    | _ b =>
      cases n using SimplexCategory.rec with
      | _ n =>
        apply NatTrans.ext
        funext q x
        induction q using Opposite.rec with | op q =>
          induction q using SimplexCategory.rec with | h r =>
            apply SSet.stdSimplex.objEquiv.injective
            ext a : 3
            exact toFinal_vertexEquiv c ⦋n⦌ (SSet.prodStdSimplex.objEquiv x a)

end

end DaggerModels.PartII.JTCommonCoefficientParameter
