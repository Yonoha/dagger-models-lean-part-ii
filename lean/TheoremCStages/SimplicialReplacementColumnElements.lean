import SimplicialSetLocalSystemElements
import NativeSimplicialReplacementWeightsChange
import NativeSimplicialReplacementReindex

/-!
# Columns of the original simplicial replacement as Elements nerves

Evaluation in one inner simplicial degree turns the complete outer
replacement into a set-valued local system. Its actual category of
elements records the same base chain and all transported labels.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.SimplicialReplacementColumnElements

universe u

noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Values of a simplicial-set diagram at the unchanged inner degree. -/
def columnValues (G : C ⥤ SSet.{u}) (k : SimplexCategoryᵒᵖ) : C ⥤ Type u :=
  G ⋙ SSet.evaluation.obj k

/-- The complete original replacement column is the exact nerve of its
set-valued category of elements. -/
def columnIso (G : C ⥤ SSet.{u}) (k : SimplexCategoryᵒᵖ) :
    (DaggerNativeSimplicialReplacement.replacement G).flip.obj k ≅
      nerve (columnValues G k).Elements :=
  SimplicialSetLocalSystemElements.localSystemElementsIso (columnValues G k)

variable (F : C ⥤ D) (G : C ⥤ SSet.{u}) (H : D ⥤ SSet.{u})
variable (η : G ⟶ F ⋙ H) (k : SimplexCategoryᵒᵖ)

/-- Apply the index functor and the complete value map to every element. -/
def elementMap :
    (columnValues G k).Elements ⥤ (columnValues H k).Elements where
  obj x := ⟨F.obj x.1, (η.app x.1).app k x.2⟩
  map {x y} a :=
    CategoryOfElements.homMk _ _ (F.map a.val) (by
      have hn := congrFun (NatTrans.congr_app (η.naturality a.val) k) x.2
      change (η.app y.1).app k ((G.map a.val).app k x.2) =
        (H.map (F.map a.val)).app k ((η.app x.1).app k x.2) at hn
      have ha : (G.map a.val).app k x.2 = y.2 := a.property
      rw [ha] at hn
      exact hn.symm)
  map_id x := by
    apply CategoryOfElements.ext (columnValues H k)
    exact F.map_id x.1
  map_comp a b := by
    apply CategoryOfElements.ext (columnValues H k)
    exact F.map_comp a.val b.val

/-- First change every original coefficient, then reindex the whole chain. -/
def replacementMap :
    DaggerNativeSimplicialReplacement.replacement G ⟶
      DaggerNativeSimplicialReplacement.replacement H :=
  DaggerNativeSimplicialReplacementWeightsChange.changeWeights η ≫
    DaggerNativeSimplicialReplacementReindex.reindex F H

private theorem eqToHom_val {L : D ⥤ Type u} {x y : L.Elements} (h : x = y) :
    (eqToHom h : x ⟶ y).val = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

/-- The column comparison carries the exact original change and reindex
map to the nerve of the actual Elements functor. -/
theorem column_triangle :
    (columnIso G k).hom ≫ nerveMap (elementMap F G H η k) =
      (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
        (replacementMap F G H η)).app k) ≫ (columnIso H k).hom := by
  apply NatTrans.ext
  funext q x
  rcases x with ⟨c, z⟩
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j a ↦ ?_)
  · refine Functor.Elements.ext _ _ rfl ?_
    simp only [eqToHom_refl, FunctorToTypes.map_id_apply]
    have hn := congrFun
      (NatTrans.congr_app
        (η.naturality (c.map (homOfLE (Fin.zero_le i)))) k) z
    change (η.app (c.obj i)).app k
        ((G.map (c.map (homOfLE (Fin.zero_le i)))).app k z) =
      (H.map (F.map (c.map (homOfLE (Fin.zero_le i))))).app k
        ((η.app (c.obj 0)).app k z) at hn
    exact hn
  · apply CategoryOfElements.ext (columnValues H k)
    simp only [CategoryOfElements.comp_val, eqToHom_val, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl

#print axioms columnIso
#print axioms elementMap
#print axioms replacementMap
#print axioms column_triangle

end

end DaggerModels.PartII.SimplicialReplacementColumnElements
