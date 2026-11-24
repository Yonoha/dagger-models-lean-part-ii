import DaggerModelsPartII.ReedyMaps

/-!
# The degree-extension boundary map from a lower diagram

The map from latching to matching in degree `n` can be constructed before
the degree-`n` object exists. This is the boundary datum used in the Reedy
degree induction for factorizations.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

def belowDegree (n : ℕ) : ObjectProperty SimplexCategoryᵒᵖ :=
  fun s ↦ s.unop.len < n

abbrev BelowDegree (n : ℕ) := (belowDegree n).FullSubcategory

def matchingBelow (n : ℕ) : MatchingIndex n ⥤ BelowDegree n where
  obj s := ⟨s.obj.right, s.property.1⟩
  map f := ObjectProperty.homMk f.hom.right

def latchingBelow (n : ℕ) : LatchingIndex n ⥤ BelowDegree n where
  obj s := ⟨s.obj.left, s.property.1⟩
  map f := ObjectProperty.homMk f.hom.left

/-- Compose a latching arrow into degree `n` with a matching arrow out of it. -/
def boundaryArrow {n : ℕ} (s : LatchingIndex n) (t : MatchingIndex n) :
    (latchingBelow n).obj s ⟶ (matchingBelow n).obj t :=
  ObjectProperty.homMk (s.obj.hom ≫ t.obj.hom)

theorem boundaryArrow_natural_matching {n : ℕ} (s : LatchingIndex n)
    {t t' : MatchingIndex n} (f : t ⟶ t') :
    boundaryArrow s t ≫ (matchingBelow n).map f = boundaryArrow s t' := by
  apply ObjectProperty.hom_ext
  change (s.obj.hom ≫ t.obj.hom) ≫ f.hom.right = s.obj.hom ≫ t'.obj.hom
  have h : t.obj.hom ≫ f.hom.right = t'.obj.hom := StructuredArrow.w f.hom
  rw [Category.assoc, h]

theorem boundaryArrow_natural_latching {n : ℕ} {s s' : LatchingIndex n}
    (f : s ⟶ s') (t : MatchingIndex n) :
    (latchingBelow n).map f ≫ boundaryArrow s' t = boundaryArrow s t := by
  apply ObjectProperty.hom_ext
  change f.hom.left ≫ s'.obj.hom ≫ t.obj.hom = s.obj.hom ≫ t.obj.hom
  have h : f.hom.left ≫ s'.obj.hom = s.obj.hom := CostructuredArrow.w f.hom
  rw [← Category.assoc, h]

noncomputable section

variable {C : Type u} [Category.{v} C]

/-- Restrict a simplicial object to degrees strictly below `n`. -/
def lowerDiagram (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) : BelowDegree n ⥤ C :=
  (belowDegree n).ι ⋙ W

/-- The compatibility cone of a fixed latching index against all matching indices. -/
def lowerBoundaryCone {n : ℕ} (W : BelowDegree n ⥤ C) (s : LatchingIndex n) :
    Cone (matchingBelow n ⋙ W) where
  pt := W.obj ((latchingBelow n).obj s)
  π :=
    { app := fun t ↦ W.map (boundaryArrow s t)
      naturality := by
        intro t t' f
        change 𝟙 _ ≫ W.map (boundaryArrow s t') =
          W.map (boundaryArrow s t) ≫ W.map ((matchingBelow n).map f)
        rw [Category.id_comp, ← W.map_comp, boundaryArrow_natural_matching] }

variable [HasLimitsOfSize.{0, 0} C]

/-- The lower-degree latching diagram has a cocone at the matching limit. -/
def lowerBoundaryCocone {n : ℕ} (W : BelowDegree n ⥤ C) :
    Cocone (latchingBelow n ⋙ W) where
  pt := limit (matchingBelow n ⋙ W)
  ι :=
    { app := fun s ↦ limit.lift _ (lowerBoundaryCone W s)
      naturality := by
        intro s s' f
        apply limit.hom_ext
        intro t
        change (W.map ((latchingBelow n).map f) ≫ limit.lift _ (lowerBoundaryCone W s')) ≫
            limit.π _ t = (limit.lift _ (lowerBoundaryCone W s) ≫ 𝟙 _) ≫ limit.π _ t
        rw [Category.comp_id, Category.assoc, limit.lift_π, limit.lift_π]
        change W.map ((latchingBelow n).map f) ≫ W.map (boundaryArrow s' t) =
          W.map (boundaryArrow s t)
        rw [← W.map_comp, boundaryArrow_natural_latching] }

variable [HasColimitsOfSize.{0, 0} C]

/-- The map `L_n W ⟶ M_n W` determined by the degrees below `n`. -/
def lowerBoundaryMap {n : ℕ} (W : BelowDegree n ⥤ C) :
    colimit (latchingBelow n ⋙ W) ⟶ limit (matchingBelow n ⋙ W) :=
  colimit.desc _ (lowerBoundaryCocone W)

/-- In a full diagram the lower-degree boundary map factors through its degree-`n` object. -/
theorem lowerBoundaryMap_factor (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    lowerBoundaryMap (lowerDiagram n W) =
      (latchingComparison n).app W ≫ (matchingComparison n).app W := by
  apply colimit.hom_ext
  intro s
  apply limit.hom_ext
  intro t
  change (colimit.ι _ s ≫ colimit.desc _ (lowerBoundaryCocone (lowerDiagram n W))) ≫
      limit.π _ t =
    (colimit.ι _ s ≫ colimit.desc _ (latchingCocone n W) ≫ limit.lift _ (matchingCone n W)) ≫
      limit.π _ t
  simp only [Category.assoc, colimit.ι_desc_assoc, lowerBoundaryCocone, limit.lift_π]
  change W.map (s.obj.hom ≫ t.obj.hom) = W.map s.obj.hom ≫ W.map t.obj.hom
  exact W.map_comp _ _

end

end DaggerModels.PartII
