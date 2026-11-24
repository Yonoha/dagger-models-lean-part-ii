import DaggerModelsPartII.ReedyExtendDiagram

/-! Relating the added-object presentation to the actual degree truncations. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

def belowDegreeInclusion {m n : ℕ} (h : m ≤ n) : BelowDegree m ⥤ BelowDegree n where
  obj s := ⟨s.obj, lt_of_lt_of_le s.property h⟩
  map f := ObjectProperty.homMk f.hom

def extensionLowerInclusion (n : ℕ) : BelowDegree n ⥤ ExtensionIndex n where
  obj := extensionIndexLower
  map f := ⟨f.hom⟩

def extensionIndexForget (n : ℕ) : ExtensionIndex n ⥤ SimplexCategoryᵒᵖ :=
  inducedFunctor (extensionIndexObj n)

theorem extensionIndex_eqToHom_hom {n : ℕ} {s t : ExtensionIndex n} (h : s = t) :
    (eqToHom h).hom = eqToHom (congrArg (extensionIndexObj n) h) := by
  cases h
  rfl

def belowToExtension (n : ℕ) : BelowDegree (n + 1) ⥤ ExtensionIndex n where
  obj s := extensionIndexOfDegree n s.obj
  map {s t} f :=
    ⟨eqToHom (extensionIndexOfDegree_obj (Nat.le_of_lt_succ s.property)) ≫ f.hom ≫
      eqToHom (extensionIndexOfDegree_obj (Nat.le_of_lt_succ t.property)).symm⟩
  map_id s := by
    apply InducedCategory.hom_ext
    simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp, eqToHom_trans,
      eqToHom_refl, InducedCategory.id_hom]
  map_comp f g := by
    apply InducedCategory.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, InducedCategory.comp_hom,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem belowToExtension_obj_old (n : ℕ) (s : BelowDegree n) :
    (belowToExtension n).obj ((belowDegreeInclusion (Nat.le_succ n)).obj s) =
      extensionIndexLower s := by
  change extensionIndexOfDegree n s.obj = extensionIndexLower s
  have hs : s.obj.unop.len < n := s.property
  simp only [extensionIndexOfDegree, dif_pos hs, extensionIndexLower]

@[simp] theorem belowToExtension_obj_top (n : ℕ) :
    (belowToExtension n).obj (degreeTop n) = extensionIndexTop n := by
  change extensionIndexOfDegree n (op ⦋n⦌) = extensionIndexTop n
  have hs : ¬ (op ⦋n⦌).unop.len < n := Nat.lt_irrefl n
  simp only [extensionIndexOfDegree, dif_neg hs, extensionIndexTop]

theorem belowInclusion_comp_belowToExtension (n : ℕ) :
    belowDegreeInclusion (Nat.le_succ n) ⋙ belowToExtension n = extensionLowerInclusion n := by
  refine CategoryTheory.Functor.ext (belowToExtension_obj_old n) ?_
  intro s t f
  apply InducedCategory.hom_ext
  change eqToHom _ ≫ f.hom ≫ eqToHom _ =
    (eqToHom (belowToExtension_obj_old n s)).hom ≫ f.hom ≫
      (eqToHom (belowToExtension_obj_old n t).symm).hom
  rw [extensionIndex_eqToHom_hom, extensionIndex_eqToHom_hom]

theorem belowToExtension_comp_forget (n : ℕ) :
    belowToExtension n ⋙ extensionIndexForget n = (belowDegree (n + 1)).ι := by
  refine CategoryTheory.Functor.ext
    (fun s ↦ extensionIndexOfDegree_obj (Nat.le_of_lt_succ s.property)) ?_
  intro s t f
  rfl

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C] {n : ℕ} {Z : BelowDegree n ⥤ C}
  (E : DegreeExtension Z)

theorem extensionLower_comp_extendedDiagram :
    extensionLowerInclusion n ⋙ extendedDiagram E = Z := by
  refine CategoryTheory.Functor.ext (F := extensionLowerInclusion n ⋙ extendedDiagram E)
    (G := Z) (fun _ ↦ rfl) ?_
  intro s t f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact extensionMap_old E ((extensionLowerInclusion n).map f)

/-- Extend a truncated diagram by the prescribed degree datum. -/
def extendBelowDiagram : BelowDegree (n + 1) ⥤ C :=
  belowToExtension n ⋙ extendedDiagram E

/-- The extension recovers the lower diagram as a functor. -/
theorem extendBelowDiagram_restrict :
    belowDegreeInclusion (Nat.le_succ n) ⋙ extendBelowDiagram E = Z := by
  change (belowDegreeInclusion (Nat.le_succ n) ⋙ belowToExtension n) ⋙ extendedDiagram E = Z
  rw [belowInclusion_comp_belowToExtension, extensionLower_comp_extendedDiagram]

/-- The new object of the extended diagram is the prescribed object. -/
theorem extendBelowDiagram_top :
    (extendBelowDiagram E).obj (degreeTop n) = E.obj := by
  change extensionObj E ((belowToExtension n).obj (degreeTop n)) = E.obj
  rw [belowToExtension_obj_top]
  rfl

/-- A compatible map of degree data extends to the actual truncations. -/
def extendBelowTransformation {T : BelowDegree n ⥤ C} {F : DegreeExtension T}
    {a : Z ⟶ T} (f : DegreeExtension.Hom a E F) :
    extendBelowDiagram E ⟶ extendBelowDiagram F :=
  Functor.whiskerLeft (belowToExtension n) (extendedTransformation E f)

section MapComparison

variable {T : BelowDegree n ⥤ C} {F : DegreeExtension T} {a : Z ⟶ T}
  (f : DegreeExtension.Hom a E F)

theorem extendBelowTransformation_app_compare (s : BelowDegree (n + 1))
    {t : ExtensionIndex n} (e : (belowToExtension n).obj s = t) :
    (extendBelowTransformation E f).app s =
      eqToHom (congrArg (extensionObj E) e) ≫ extensionTransformationApp E f t ≫
        eqToHom (congrArg (extensionObj F) e.symm) := by
  subst t
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- In every lower degree the extended transformation is the given one. -/
theorem extendBelowTransformation_app_old (s : BelowDegree n) :
    (extendBelowTransformation E f).app ((belowDegreeInclusion (Nat.le_succ n)).obj s) =
      eqToHom (CategoryTheory.Functor.congr_obj (extendBelowDiagram_restrict E) s) ≫
        a.app s ≫
      eqToHom (CategoryTheory.Functor.congr_obj (extendBelowDiagram_restrict F) s).symm :=
  extendBelowTransformation_app_compare E f _ (belowToExtension_obj_old n s)

/-- At the new degree the extended transformation is the prescribed degree map. -/
theorem extendBelowTransformation_app_top :
    (extendBelowTransformation E f).app (degreeTop n) =
      eqToHom (extendBelowDiagram_top E) ≫ f.app ≫ eqToHom (extendBelowDiagram_top F).symm :=
  extendBelowTransformation_app_compare E f _ (belowToExtension_obj_top n)

end MapComparison

/-- The extension respects a factorization of maps on both the lower diagram and the new object. -/
theorem extendBelowTransformation_comp_of_fac
    {T S : BelowDegree n ⥤ C} {F : DegreeExtension T} {G : DegreeExtension S}
    {a : Z ⟶ T} {b : T ⟶ S} {c : Z ⟶ S}
    (f : DegreeExtension.Hom a E F) (g : DegreeExtension.Hom b F G)
    (h : DegreeExtension.Hom c E G) (hLower : a ≫ b = c)
    (hTop : f.app ≫ g.app = h.app) :
    extendBelowTransformation E f ≫ extendBelowTransformation F g =
      extendBelowTransformation E h := by
  have he : extendedTransformation E f ≫ extendedTransformation F g =
      extendedTransformation E h := by
    ext s
    cases s with
    | none => exact hTop
    | some s => exact NatTrans.congr_app hLower s
  exact congrArg ((CategoryTheory.Functor.whiskeringLeft _ _ _).obj
    (belowToExtension n)).map he

end

end DaggerModels.PartII
