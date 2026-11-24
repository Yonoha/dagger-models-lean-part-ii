import SimplicialSetLocalSystem
import Mathlib.CategoryTheory.Elements

/-!
# A set-valued local system and its category of elements

A simplex is a complete chain in the base category together with an element
at its initial object. Transport along the chain gives the exact nerve of
the category of elements. The comparison retains the base chain.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerNativeSimplicialReplacementCells
open DaggerModels.PartII.SimplicialSetLocalSystem

namespace DaggerModels.PartII.SimplicialSetLocalSystemElements

universe u

variable {C : Type u} [Category.{u} C] (L : C ⥤ Type u)

private theorem eqToHom_val {a b : L.Elements} (h : a = b) :
    (eqToHom h : a ⟶ b).val = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

private def toElementsChain {q : SimplexCategoryᵒᵖ}
    (x : (localSystem L).obj q) : (nerve L.Elements).obj q where
  obj i :=
    ⟨x.1.obj i, L.map (x.1.map (homOfLE (Fin.zero_le i))) x.2⟩
  map {i j} a :=
    CategoryOfElements.homMk _ _ (x.1.map a) (by
      change L.map (x.1.map a)
          (L.map (x.1.map (homOfLE (Fin.zero_le i))) x.2) =
        L.map (x.1.map (homOfLE (Fin.zero_le j))) x.2
      rw [← FunctorToTypes.map_comp_apply, ← x.1.map_comp]
      exact congrArg (fun t ↦ L.map (x.1.map t) x.2)
        (Subsingleton.elim _ _))
  map_id i := by
    apply CategoryOfElements.ext L
    exact x.1.map_id i
  map_comp a b := by
    apply CategoryOfElements.ext L
    exact x.1.map_comp a b

private def fromElementsChain {q : SimplexCategoryᵒᵖ}
    (A : (nerve L.Elements).obj q) : (localSystem L).obj q :=
  ⟨A ⋙ CategoryOfElements.π L, (A.obj 0).2⟩

private theorem from_to {q : SimplexCategoryᵒᵖ}
    (x : (localSystem L).obj q) :
    fromElementsChain L (toElementsChain L x) = x := by
  rcases x with ⟨A, x⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change L.map (A.map (homOfLE (Fin.zero_le (0 : Fin (q.unop.len + 1))))) x = x
    simp

private theorem to_from {q : SimplexCategoryᵒᵖ}
    (A : (nerve L.Elements).obj q) :
    toElementsChain L (fromElementsChain L A) = A := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j a ↦ ?_)
  · refine Functor.Elements.ext _ _ rfl ?_
    simpa only [eqToHom_refl, FunctorToTypes.map_id_apply] using
      (CategoryOfElements.map_snd (A.map (homOfLE (Fin.zero_le i))))
  · apply CategoryOfElements.ext L
    simp only [CategoryOfElements.comp_val, eqToHom_val, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl

private def degreeEquiv (q : SimplexCategoryᵒᵖ) :
    (localSystem L).obj q ≃ (nerve L.Elements).obj q where
  toFun := toElementsChain L
  invFun := fromElementsChain L
  left_inv := from_to L
  right_inv := to_from L

private theorem degreeEquiv_natural {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (x : (localSystem L).obj q) :
    (degreeEquiv L r) ((localSystem L).map α x) =
      (nerve L.Elements).map α ((degreeEquiv L q) x) := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j a ↦ ?_)
  · refine Functor.Elements.ext _ _ rfl ?_
    simp only [eqToHom_refl, FunctorToTypes.map_id_apply]
    rcases x with ⟨A, x⟩
    change L.map (((nerve C).map α A).map
        (homOfLE (Fin.zero_le i))) (L.map (initialArrow α A) x) =
      L.map (A.map (homOfLE (Fin.zero_le
        ((SimplexCategory.toCat.map α.unop).toFunctor.obj i)))) x
    rw [← FunctorToTypes.map_comp_apply]
    have hm : initialArrow α A ≫
        ((nerve C).map α A).map (homOfLE (Fin.zero_le i)) =
      A.map (homOfLE (Fin.zero_le
        ((SimplexCategory.toCat.map α.unop).toFunctor.obj i))) := by
      change A.map _ ≫ A.map _ = A.map _
      rw [← A.map_comp]
      congr 1
    exact congrArg (fun t ↦ L.map t x) hm
  · apply CategoryOfElements.ext L
    simp only [CategoryOfElements.comp_val, eqToHom_val, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl

/-- Exact simplicial isomorphism with the nerve of the category of elements. -/
def localSystemElementsIso : localSystem L ≅ nerve L.Elements :=
  NatIso.ofComponents (fun q ↦ (degreeEquiv L q).toIso) (by
    intro q r α
    funext x
    exact degreeEquiv_natural L α x)

/-- The isomorphism preserves the entire base chain, not only vertices. -/
theorem projection_triangle :
    (localSystemElementsIso L).hom ≫
        nerveMap (CategoryOfElements.π L) = projection L := by
  apply NatTrans.ext
  funext q x
  rfl

#print axioms localSystem
#print axioms localSystemElementsIso
#print axioms projection_triangle

end DaggerModels.PartII.SimplicialSetLocalSystemElements
