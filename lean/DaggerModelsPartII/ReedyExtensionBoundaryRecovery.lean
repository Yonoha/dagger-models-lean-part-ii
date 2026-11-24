import DaggerModelsPartII.ReedyTruncateExtension

/-! Recover the chosen latching and matching legs after reindexing the degree extension. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite

universe v u

namespace DaggerModels.PartII

variable {n : ℕ}

theorem belowToExtension_map_compare {s t : BelowDegree (n + 1)} (f : s ⟶ t)
    {s' t' : ExtensionIndex n}
    (hs : (belowToExtension n).obj s = s') (ht : (belowToExtension n).obj t = t')
    (g : s' ⟶ t') (hs' : extensionIndexObj n s' = s.obj)
    (ht' : extensionIndexObj n t' = t.obj)
    (hg : g.hom = eqToHom hs' ≫ f.hom ≫ eqToHom ht'.symm) :
    (belowToExtension n).map f = eqToHom hs ≫ g ≫ eqToHom ht.symm := by
  apply InducedCategory.hom_ext
  simp only [InducedCategory.comp_hom, extensionIndex_eqToHom_hom, hg, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  rfl

/-- A matching face in the actual degree truncation. -/
def truncatedMatchingArrow (s : MatchingIndex n) :
    degreeTop n ⟶ (belowDegreeInclusion (Nat.le_succ n)).obj ((matchingBelow n).obj s) :=
  ObjectProperty.homMk s.obj.hom

/-- A latching arrow in the actual degree truncation. -/
def truncatedLatchingArrow (s : LatchingIndex n) :
    (belowDegreeInclusion (Nat.le_succ n)).obj ((latchingBelow n).obj s) ⟶ degreeTop n :=
  ObjectProperty.homMk s.obj.hom

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]
  {Z : BelowDegree n ⥤ C} (E : DegreeExtension Z)

theorem extendBelowDiagram_map_compare {s t : BelowDegree (n + 1)} (f : s ⟶ t)
    {s' t' : ExtensionIndex n}
    (hs : (belowToExtension n).obj s = s') (ht : (belowToExtension n).obj t = t')
    (g : s' ⟶ t') (h : (belowToExtension n).map f = eqToHom hs ≫ g ≫ eqToHom ht.symm) :
    (extendBelowDiagram E).map f =
      eqToHom (congrArg (extensionObj E) hs) ≫ extensionMap E g ≫
        eqToHom (congrArg (extensionObj E) ht.symm) := by
  change (extendedDiagram E).map ((belowToExtension n).map f) = _
  rw [h]
  simp only [(extendedDiagram E).map_comp, eqToHom_map]
  rfl

/-- The face maps of the extension are the components of the chosen matching leg. -/
theorem extendBelowDiagram_map_matching (s : MatchingIndex n) :
    (extendBelowDiagram E).map (truncatedMatchingArrow s) =
      eqToHom (extendBelowDiagram_top E) ≫
        (E.toMatching ≫ limit.π (matchingBelow n ⋙ Z) s) ≫
      eqToHom (CategoryTheory.Functor.congr_obj (extendBelowDiagram_restrict E)
        ((matchingBelow n).obj s)).symm := by
  let g : extensionIndexTop n ⟶ extensionIndexLower ((matchingBelow n).obj s) := ⟨s.obj.hom⟩
  have hg : Mono g.hom.unop := s.property.2
  have hs := belowToExtension_obj_top n
  have ht := belowToExtension_obj_old n ((matchingBelow n).obj s)
  have h := belowToExtension_map_compare (truncatedMatchingArrow s) hs ht g rfl rfl (by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)
  rw [extendBelowDiagram_map_compare E _ hs ht g h, extensionMap_of_inverse E g hg]
  rfl

/-- The degeneracy maps of the extension are the components of the chosen latching leg. -/
theorem extendBelowDiagram_map_latching (s : LatchingIndex n) :
    (extendBelowDiagram E).map (truncatedLatchingArrow s) =
      eqToHom (CategoryTheory.Functor.congr_obj (extendBelowDiagram_restrict E)
        ((latchingBelow n).obj s)) ≫
        (colimit.ι (latchingBelow n ⋙ Z) s ≫ E.fromLatching) ≫
      eqToHom (extendBelowDiagram_top E).symm := by
  let g : extensionIndexLower ((latchingBelow n).obj s) ⟶ extensionIndexTop n := ⟨s.obj.hom⟩
  have hg : Epi g.hom.unop := s.property.2
  have hs := belowToExtension_obj_old n ((latchingBelow n).obj s)
  have ht := belowToExtension_obj_top n
  have h := belowToExtension_map_compare (truncatedLatchingArrow s) hs ht g rfl rfl (by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)
  rw [extendBelowDiagram_map_compare E _ hs ht g h, extensionMap_of_direct E g hg]
  rfl

end

end DaggerModels.PartII
