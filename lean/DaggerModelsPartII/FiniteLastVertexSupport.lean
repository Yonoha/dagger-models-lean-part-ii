import DaggerModelsPartII.FiniteSupportWeakCover

/-! Descend a contraction supported on finitely many simplices of a weak last-vertex cover. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiniteLastVertexSupport

open NerveSimplexResolutionHomotopy (lastVertexOnSubcomplex comparisonOnSubcomplex)
open SimplicialResolutionFunctor (augmentation augmentation_weak elementsProjection)

noncomputable section

private abbrev toPoint (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

variable {C D : Type} [SmallCategory C] [SmallCategory D]
variable (A : (nerve C).Subcomplex) (p : D ⥤ A.toSSet.Elementsᵒᵖ) (e : D ⥤ C)

private abbrev L := lastVertexOnSubcomplex C A

/-- The actual evaluation is nullhomotopic on each finite support in the cover. -/
def SupportNullhomotopies : Prop :=
  ∀ S : (nerve D).Subcomplex, S.toSSet.IsFinite →
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve C,
      Nonempty (SSet.Homotopy (R.map (S.ι ≫ nerveMap e)) (R.map (toPoint S.toSSet ≫ v)))

private theorem projection_nullhomotopies (t : e ⟶ p ⋙ L A) (h : SupportNullhomotopies e)
    (S : (nerve D).Subcomplex) (hS : S.toSSet.IsFinite) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve C,
      Nonempty (SSet.Homotopy (R.map (S.ι ≫ nerveMap p ≫ nerveMap (L A)))
        (R.map (toPoint S.toSSet ≫ v))) := by
  obtain ⟨v, ⟨H⟩⟩ := h S hS
  let K := (natTransHomotopyR t).precomp (R.map S.ι)
  have K' : SSet.Homotopy (R.map (S.ι ≫ nerveMap e))
      (R.map (S.ι ≫ nerveMap p ≫ nerveMap (L A))) :=
    K.congr (R.map_comp _ _).symm (R.map_comp _ _).symm
  exact ⟨v, ⟨K'.symm.trans H⟩⟩

/-- A contraction on each finite support suffices to contract the literal
inclusion of the original subcomplex. -/
theorem inclusion_nullhomotopic [WeakEquivalence (nerveMap p)] (hA : A.toSSet.IsFinite)
    (t : e ⟶ p ⋙ L A) (h : SupportNullhomotopies e) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve C,
      Nonempty (SSet.Homotopy (R.map A.ι) (R.map (toPoint A.toSSet ≫ v))) := by
  let a := augmentation.app A.toSSet
  let b := elementsProjection.app A.toSSet
  let η := sSetTopAdj.unit.app A.toSSet
  let l := nerveMap (L A)
  letI : A.toSSet.IsFinite := hA
  letI := augmentation_weak A.toSSet
  obtain ⟨g, ⟨H⟩⟩ := FiniteSupportWeakCover.exists_homotopy_lift
    (A := A.toSSet) a η
  obtain ⟨v, ⟨K⟩⟩ := FiniteSupportWeakCover.nullhomotopic
    (A := A.toSSet) (nerveMap p) l (g ≫ R.map b)
    (projection_nullhomotopies A p e t h)
  let M := ((comparisonOnSubcomplex C A).toTop.toSSet).precomp g
  have M' : SSet.Homotopy ((g ≫ R.map a) ≫ R.map A.ι)
      ((g ≫ R.map b) ≫ R.map l) := by
    refine M.congr ?_ ?_
    · change g ≫ R.map (a ≫ A.ι) = _
      rw [R.map_comp, Category.assoc]
    · change g ≫ R.map (b ≫ l) = _
      rw [R.map_comp, Category.assoc]
  have hpoint : toPoint A.toSSet ≫ sSetTopAdj.unit.app (Δ[0] : SSet.{0}) ≫ R.map v =
      η ≫ R.map (toPoint A.toSSet ≫ v) := by
    have ht : toPoint A.toSSet ≫ sSetTopAdj.unit.app (Δ[0] : SSet.{0}) =
        η ≫ R.map (toPoint A.toSSet) := sSetTopAdj.unit.naturality (toPoint A.toSSet)
    rw [← Category.assoc, ht, Category.assoc, R.map_comp]
  have H' := SSet.Homotopy.postcomp H.symm (R.map A.ι)
  exact ⟨v, ⟨FiniteWeakCover.homotopyOfPrecomp η ((H'.trans (M'.trans K)).congr rfl hpoint)⟩⟩

end
end DaggerModels.PartII.FiniteLastVertexSupport
