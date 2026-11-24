import DaggerModelsPartII.ReedyTruncateExtension

/-! The degree-extension construction recovers existing simplicial diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]
  (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C)

theorem extensionOfDiagram_obj (s : ExtensionIndex n) :
    extensionObj (DegreeExtension.ofDiagram n W) s = W.obj (extensionIndexObj n s) := by
  cases s <;> rfl

theorem extensionOfDiagram_inverse {s t : ExtensionIndex n} (f : s ⟶ t)
    (hf : Mono f.hom.unop) :
    extensionInverseMap (DegreeExtension.ofDiagram n W) f hf =
      eqToHom (extensionOfDiagram_obj n W s) ≫ W.map f.hom ≫
        eqToHom (extensionOfDiagram_obj n W t).symm := by
  cases s with
  | none =>
    cases t with
    | none =>
      have h := extensionInverse_endomorphism_eq_id f hf
      subst f
      simp only [extensionInverseMap_id, eqToHom_refl, InducedCategory.id_hom, W.map_id,
        Category.id_comp]
      rfl
    | some t =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact limit.lift_π (matchingCone n W) (extensionMatchingIndex f hf)
  | some s =>
    cases t with
    | none => exact (extensionInverse_not_raise f hf).elim
    | some t =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl

theorem extensionOfDiagram_direct {s t : ExtensionIndex n} (f : s ⟶ t)
    (hf : Epi f.hom.unop) :
    extensionDirectMap (DegreeExtension.ofDiagram n W) f hf =
      eqToHom (extensionOfDiagram_obj n W s) ≫ W.map f.hom ≫
        eqToHom (extensionOfDiagram_obj n W t).symm := by
  cases s with
  | none =>
    cases t with
    | none =>
      have h := extensionDirect_endomorphism_eq_id f hf
      subst f
      simp only [extensionDirectMap_id, eqToHom_refl, InducedCategory.id_hom, W.map_id,
        Category.id_comp]
      rfl
    | some t => exact (extensionDirect_not_lower f hf).elim
  | some s =>
    cases t with
    | none =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact colimit.ι_desc (latchingCocone n W) (extensionLatchingIndex f hf)
    | some t =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl

/-- Applying the extension to the degree data of a full diagram recovers its restriction. -/
theorem extendedDiagram_ofDiagram :
    extendedDiagram (DegreeExtension.ofDiagram n W) = extensionIndexForget n ⋙ W := by
  refine CategoryTheory.Functor.ext (extensionOfDiagram_obj n W) ?_
  intro s t f
  let F := extensionIndexFactor f
  change extensionMap (DegreeExtension.ofDiagram n W) f =
    eqToHom (extensionOfDiagram_obj n W s) ≫ W.map f.hom ≫
      eqToHom (extensionOfDiagram_obj n W t).symm
  rw [extensionMap_of_factor _ F, extensionOfDiagram_inverse n W F.inverse F.inverse_mono,
    extensionOfDiagram_direct n W F.direct F.direct_epi]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← W.map_comp_assoc]
  exact congrArg (fun k ↦ eqToHom (extensionOfDiagram_obj n W s) ≫ W.map k ≫
    eqToHom (extensionOfDiagram_obj n W t).symm) (congrArg InducedCategory.Hom.hom F.fac)

/-- Recovery on the actual degree truncation. -/
theorem extendBelowDiagram_ofDiagram :
    extendBelowDiagram (DegreeExtension.ofDiagram n W) = lowerDiagram (n + 1) W := by
  unfold extendBelowDiagram
  rw [extendedDiagram_ofDiagram]
  change (belowToExtension n ⋙ extensionIndexForget n) ⋙ W = lowerDiagram (n + 1) W
  rw [belowToExtension_comp_forget]
  rfl

/-- Extension recovers the components of an existing natural transformation. -/
theorem extendBelowTransformation_ofDiagram_app
    {V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) (s : BelowDegree (n + 1)) :
    (extendBelowTransformation (DegreeExtension.ofDiagram n W)
      (DegreeExtension.Hom.ofDiagram f n)).app s =
      eqToHom (CategoryTheory.Functor.congr_obj (extendBelowDiagram_ofDiagram n W) s) ≫
        f.app s.obj ≫
      eqToHom (CategoryTheory.Functor.congr_obj (extendBelowDiagram_ofDiagram n V) s).symm := by
  by_cases hs : s.obj.unop.len < n
  · exact extendBelowTransformation_app_old (DegreeExtension.ofDiagram n W)
      (DegreeExtension.Hom.ofDiagram f n) ⟨s.obj, hs⟩
  · obtain rfl := eq_degreeTop_of_not_below s hs
    exact extendBelowTransformation_app_top (DegreeExtension.ofDiagram n W)
      (DegreeExtension.Hom.ofDiagram f n)

end

end DaggerModels.PartII
