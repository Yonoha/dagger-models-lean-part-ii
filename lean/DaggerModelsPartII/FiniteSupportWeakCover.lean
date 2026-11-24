import DaggerModelsPartII.FiniteLastVertexFactor

/-! A weak cover can be used via its finite simplicial supports. -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiniteSupportWeakCover

noncomputable section

variable {A X Y : SSet.{0}}

private abbrev R : SSet.{0} ⥤ SSet.{0} := SSet.toTop.{0} ⋙ TopCat.toSSet
private abbrev toPoint (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

/-- Lift a map through a Kan weak equivalence after singular realization. -/
theorem exists_homotopy_lift (p : X ⟶ Y) [WeakEquivalence p] (f : A ⟶ R.obj Y) :
    ∃ g : A ⟶ R.obj X, Nonempty (SSet.Homotopy (g ≫ R.map p) f) := by
  haveI : WeakEquivalence (R.map p) := FiniteWeakCover.weak_singular p
  obtain ⟨c, hc⟩ := (LeftHomotopyClass.postcomp_bijective_of_weakEquivalence A (R.map p)).2
    (LeftHomotopyClass.mk f)
  obtain ⟨g, rfl⟩ := c.mk_surjective
  change (LeftHomotopyClass.mk g).postcomp (R.map p) = LeftHomotopyClass.mk f at hc
  rw [LeftHomotopyClass.postcomp_mk, LeftHomotopyClass.mk_eq_mk_iff] at hc
  exact ⟨g, ⟨DaggerStandardSSetCylinder.literalOfModel hc⟩⟩

/-- A map from a finite simplicial set into the singular realization of a
weak cover's target lifts up to homotopy through a finite support in the cover. -/
theorem exists_lift (p : X ⟶ Y) [WeakEquivalence p] [A.IsFinite]
    (f : A ⟶ R.obj Y) :
    ∃ (S : X.Subcomplex) (_ : S.toSSet.IsFinite) (g : A ⟶ R.obj S.toSSet),
      Nonempty (SSet.Homotopy (g ≫ R.map (S.ι ≫ p)) f) := by
  obtain ⟨g, ⟨H⟩⟩ := exists_homotopy_lift p f
  let e := sSetTopAdj.homEquiv A (SSet.toTop.obj X)
  obtain ⟨S, hS, k, hk⟩ := SSet.exists_factor_thru_finite_of_topCatHom (e.symm g)
  let gS := (sSetTopAdj.homEquiv A (SSet.toTop.obj S.toSSet)) k
  have he : gS ≫ R.map S.ι = g := by
    change gS ≫ TopCat.toSSet.map (SSet.toTop.map S.ι) = g
    rw [← sSetTopAdj.homEquiv_naturality_right, ← hk]
    exact e.apply_symm_apply g
  refine ⟨S, hS, gS, ⟨H.congr ?_ rfl⟩⟩
  rw [R.map_comp, ← Category.assoc, he]

/-- A contraction on finite supports of a weak cover suffices for an
arbitrary map into its target from a finite simplicial set. -/
theorem nullhomotopic (p : X ⟶ Y) [WeakEquivalence p] {Z : SSet.{0}} (q : Y ⟶ Z)
    [A.IsFinite] (f : A ⟶ R.obj Y)
    (h : ∀ S : X.Subcomplex, S.toSSet.IsFinite →
      ∃ v : (Δ[0] : SSet.{0}) ⟶ Z,
        Nonempty (SSet.Homotopy (R.map (S.ι ≫ p ≫ q)) (R.map (toPoint S.toSSet ≫ v)))) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ Z,
      Nonempty (SSet.Homotopy (f ≫ R.map q) (toPoint A ≫ sSetTopAdj.unit.app _ ≫ R.map v)) := by
  obtain ⟨S, hS, g, ⟨H⟩⟩ := exists_lift p f
  obtain ⟨v, ⟨K⟩⟩ := h S hS
  have hs : g ≫ R.map (toPoint S.toSSet) = toPoint A ≫ sSetTopAdj.unit.app _ :=
    (SSet.stdSimplex.isTerminalObj₀.isTerminalObj R).hom_ext _ _
  have H' : SSet.Homotopy (f ≫ R.map q) (g ≫ R.map (S.ι ≫ p ≫ q)) := by
    refine SSet.Homotopy.congr (SSet.Homotopy.postcomp H.symm (R.map q)) rfl ?_
    simp only [R.map_comp, Category.assoc]
  have K' : SSet.Homotopy (g ≫ R.map (S.ι ≫ p ≫ q)) (toPoint A ≫ sSetTopAdj.unit.app _ ≫ R.map v) := by
    refine SSet.Homotopy.congr (K.precomp g) rfl ?_
    rw [R.map_comp, ← Category.assoc, hs, Category.assoc]
  exact ⟨v, ⟨H'.trans K'⟩⟩

end
end DaggerModels.PartII.FiniteSupportWeakCover
