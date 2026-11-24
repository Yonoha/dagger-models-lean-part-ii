import TopCatModelCategory.QuillenAdjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# A Quillen adjunction with identity left functor up to natural isomorphism

For a single model structure, a natural isomorphism from the left adjoint to
the identity identifies its image of every arrow with that same arrow in the
arrow category. The adjunction counit is an isomorphism, so the defining
weak-equivalence test for a Quillen equivalence follows directly. No
cofibrancy or fibrancy assumption is added beyond the test's own indices.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra

universe u v

namespace DaggerModels.PartII.AdjunctionLeftIdentityQuillenEquivalence

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {F G : C ⥤ C}

noncomputable section

/-- An endo-Quillen adjunction whose left adjoint is naturally the identity
is a Quillen equivalence for the unchanged model structure. -/
theorem of_left_identity (adj : F ⊣ G) [adj.IsQuillenAdjunction]
    (e : F ≅ 𝟭 C) : adj.IsQuillenEquivalence := by
  letI : F.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  haveI : IsIso adj.counit := inferInstance
  refine {
    toIsQuillenAdjunction := inferInstance
    weakEquivalence_homEquiv_iff := ?_ }
  intro A X hA hX f
  let g : A ⟶ G.obj X := (adj.homEquiv A X) f
  have hfactor : F.map g ≫ adj.counit.app X = f := by
    change F.map ((adj.homEquiv A X) f) ≫ adj.counit.app X = f
    exact (adj.homEquiv A X).symm_apply_apply f
  let arrowIso : Arrow.mk (F.map g) ≅ Arrow.mk g :=
    Arrow.isoMk (e.app A) (e.app (G.obj X)) (by
      simpa only [Functor.id_map] using (e.hom.naturality g).symm)
  have hmap : WeakEquivalence (F.map g) ↔ WeakEquivalence g := by
    simp only [weakEquivalence_iff]
    exact (weakEquivalences C).arrow_mk_iso_iff arrowIso
  haveI : WeakEquivalence (adj.counit.app X) := inferInstance
  have hcomp : WeakEquivalence (F.map g ≫ adj.counit.app X) ↔
      WeakEquivalence (F.map g) := weakEquivalence_postcomp_iff _ _
  change WeakEquivalence g ↔ WeakEquivalence f
  rw [← hfactor]
  exact hmap.symm.trans hcomp.symm

#print axioms of_left_identity

end

end DaggerModels.PartII.AdjunctionLeftIdentityQuillenEquivalence
