import SimplicialReplacementColumnElements
import SimplicialSetLocalSystemMorphismFibration

/-!
# Vertical naturality of the complete replacement-column comparison

The columnwise category-of-elements isomorphism retains every original
outer chain. Its compatibility with an inner operator is the naturality
of the category-of-elements construction under a map of set-valued
diagrams.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerNativeSimplicialReplacementCells
open DaggerModels.PartII.SimplicialSetLocalSystem
open DaggerModels.PartII.SimplicialSetLocalSystemElements
open DaggerModels.PartII.SimplicialSetLocalSystemMorphismFibration
open DaggerModels.PartII.SimplicialReplacementColumnElements

namespace DaggerModels.PartII.ColumnElementsVerticalNaturality

universe u

noncomputable section

variable {C : Type u} [Category.{u} C]

private theorem eqToHom_val {M : C ⥤ Type u} {a b : M.Elements} (h : a = b) :
    (eqToHom h : a ⟶ b).val = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

/-- The complete local-system/Elements comparison is natural under an
arbitrary transformation of set-valued diagrams. -/
theorem localSystemElementsIso_natural {L M : C ⥤ Type u} (ψ : L ⟶ M) :
    (localSystemElementsIso L).hom ≫ nerveMap (NatTrans.mapElements ψ) =
      mapSystem ψ ≫ (localSystemElementsIso M).hom := by
  apply NatTrans.ext
  funext q z
  rcases z with ⟨c, x⟩
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j a ↦ ?_)
  · refine Functor.Elements.ext _ _ rfl ?_
    simp only [eqToHom_refl, FunctorToTypes.map_id_apply]
    have hn := congrFun (ψ.naturality (c.map (homOfLE (Fin.zero_le i)))) x
    change ψ.app (c.obj i)
        (L.map (c.map (homOfLE (Fin.zero_le i))) x) =
      M.map (c.map (homOfLE (Fin.zero_le i))) (ψ.app (c.obj 0) x) at hn
    exact hn
  · apply CategoryOfElements.ext M
    simp only [CategoryOfElements.comp_val, eqToHom_val, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl

/-- The checked column isomorphism commutes with the actual inner
simplicial operator of the original complete replacement. -/
theorem columnIso_vertical_naturality (G : C ⥤ SSet.{u})
    {k l : SimplexCategoryᵒᵖ} (β : k ⟶ l) :
    (columnIso G k).hom ≫
        (G.flip ⋙ Functor.elementsFunctor ⋙ nerveFunctor).map β =
      (DaggerNativeSimplicialReplacement.replacement G).flip.map β ≫
        (columnIso G l).hom := by
  change (localSystemElementsIso (G.flip.obj k)).hom ≫
      nerveMap (NatTrans.mapElements (G.flip.map β)) =
    mapSystem (G.flip.map β) ≫
      (localSystemElementsIso (G.flip.obj l)).hom
  exact localSystemElementsIso_natural (G.flip.map β)

/-- The fixed-column isomorphisms assemble in the unchanged inner
direction, with the full outer chains and all their values retained. -/
def columnsIso (G : C ⥤ SSet.{u}) :
    (DaggerNativeSimplicialReplacement.replacement G).flip ≅
      G.flip ⋙ Functor.elementsFunctor ⋙ nerveFunctor :=
  NatIso.ofComponents (columnIso G) (by
    intro k l β
    exact (columnIso_vertical_naturality G β).symm)

#print axioms localSystemElementsIso_natural
#print axioms columnIso_vertical_naturality
#print axioms columnsIso

end

end DaggerModels.PartII.ColumnElementsVerticalNaturality
