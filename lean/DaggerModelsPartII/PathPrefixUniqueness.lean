import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Uniqueness of a path prefix with its splitting vertex

Mathlib's path cancellation applies after the intermediate vertex is fixed.
The vertex list first identifies that vertex from the composite and the
prefix length, so cancellation can retain all endpoint information.
-/

set_option autoImplicit false

namespace DaggerModels.PartII.PathPrefixUniqueness

/-- Equal whole paths and equal prefix lengths determine the splitting
vertex and both factors, even if the vertex was not fixed in advance. -/
theorem factors_heq_of_comp_eq_of_length_eq
    {V : Type*} [Quiver V] {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c)
    (p' : Quiver.Path a d) (q' : Quiver.Path d c)
    (hcomp : p.comp q = p'.comp q') (hlen : p.length = p'.length) :
    b = d ∧ p ≍ p' ∧ q ≍ q' := by
  have hp := Quiver.Path.vertices_comp_get_length_eq p q
  have hp' := Quiver.Path.vertices_comp_get_length_eq p' q'
  have hb : (p.comp q).vertices[p.length]? = some b :=
    List.getElem?_eq_some_iff.mpr ⟨by simp, hp⟩
  have hd : (p'.comp q').vertices[p'.length]? = some d :=
    List.getElem?_eq_some_iff.mpr ⟨by simp, hp'⟩
  have hbd : b = d := Option.some.inj (by
    calc
      some b = (p.comp q).vertices[p.length]? := hb.symm
      _ = (p'.comp q').vertices[p'.length]? := by rw [hcomp, hlen]
      _ = some d := hd)
  subst d
  obtain ⟨rfl, rfl⟩ := (Quiver.Path.comp_inj' hlen).mp hcomp
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

end DaggerModels.PartII.PathPrefixUniqueness
