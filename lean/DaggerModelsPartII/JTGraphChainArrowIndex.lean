import DaggerModelsPartII.JTGraphSimplexLastVertex

/-! The original composite arrow of every original nerve simplex. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphChainArrowIndex

open JTGraphCylinderSimplexSpan (Simplices firstVertex)
open JTGraphSimplexLastVertex (lastVertex lastVertex_weak)
open DaggerNativeSimplicialReplacementCells (first initialArrow)
open DaggerNativeDualTheoremACells (last lastArrow)

noncomputable section

variable (C : Type) [SmallCategory C]

private abbrev ends := (firstVertex C).op.prod' (lastVertex C)

private def chainArrow (P : (nerve C).Elements) : first P.snd ⟶ last P.snd :=
  P.snd.map (homOfLE (Fin.zero_le (Fin.last P.fst.unop.len)))

private theorem chain_factor {P P' : (nerve C).Elements} (f : P ⟶ P') :
    (firstVertex C).map f ≫ chainArrow C P' ≫ (lastVertex C).map f.op = chainArrow C P := by
  rcases P with ⟨p, u⟩
  rcases P' with ⟨q, v⟩
  rcases f with ⟨j, h⟩
  change p ⟶ q at j
  change (nerve C).map j u = v at h
  subst v
  change (initialArrow j u ≫ eqToHom _) ≫ _ ≫ (eqToHom _ ≫ lastArrow j u) = _
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change u.map _ ≫ u.map _ ≫ u.map _ = u.map _
  rw [← u.map_comp, ← u.map_comp]
  congr 1

/-- A simplex is sent to its actual first-to-last composite. Every operator
supplies the actual prefix and suffix of the larger chain. -/
def chainIndex : Simplices C ⥤ (Functor.hom C).Elements where
  obj P := ⟨(ends C).obj P, chainArrow C P.unop⟩
  map f := ⟨(ends C).map f, chain_factor C f.unop⟩
  map_id P := CategoryOfElements.ext _ _ _ ((ends C).map_id P)
  map_comp f g := CategoryOfElements.ext _ _ _ ((ends C).map_comp f g)

/-- Recover the actual last vertex and suffix from the arrow factorization. -/
abbrev target : (Functor.hom C).Elements ⥤ C :=
  CategoryOfElements.π (Functor.hom C) ⋙ CategoryTheory.Prod.snd Cᵒᵖ C

theorem chainIndex_target : chainIndex C ⋙ target C = lastVertex C := by
  rfl

/-- The last vertex obtained from the composite-arrow indexing is Kan weak. -/
theorem last_weak : WeakEquivalence (nerveMap (chainIndex C ⋙ target C)) := by
  rw [chainIndex_target]
  exact lastVertex_weak C

end

end DaggerModels.PartII.JTGraphChainArrowIndex
