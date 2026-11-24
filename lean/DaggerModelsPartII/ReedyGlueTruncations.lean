import DaggerModelsPartII.ReedyTruncateExtension

/-! Glue compatible finite truncations to a simplicial diagram. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe v u

namespace DaggerModels.PartII

variable {C : Type u} [Category.{v} C]

theorem belowDegreeInclusion_comp {j k m : ℕ} (h : j ≤ k) (h' : k ≤ m) :
    belowDegreeInclusion h ⋙ belowDegreeInclusion h' = belowDegreeInclusion (h.trans h') := rfl

/-- A sequence of truncated diagrams with compatible restrictions. -/
structure DiagramTower (C : Type u) [Category.{v} C] where
  stage (n : ℕ) : BelowDegree n ⥤ C
  step (n : ℕ) : belowDegreeInclusion (Nat.le_succ n) ⋙ stage (n + 1) = stage n

variable (T : DiagramTower C)

theorem diagramTower_restrict {j k : ℕ} (h : j ≤ k) :
    belowDegreeInclusion h ⋙ T.stage k = T.stage j := by
  induction h with
  | refl => rfl
  | @step k h ih =>
    calc
      _ = (belowDegreeInclusion h ⋙ belowDegreeInclusion (Nat.le_succ k)) ⋙
          T.stage (k + 1) := rfl
      _ = belowDegreeInclusion h ⋙ T.stage k := by
        change belowDegreeInclusion h ⋙
          (belowDegreeInclusion (Nat.le_succ k) ⋙ T.stage (k + 1)) = _
        rw [T.step]
      _ = T.stage j := ih

/-- Use the smallest truncation containing the object. -/
def diagramTowerObj (s : SimplexCategoryᵒᵖ) : C :=
  (T.stage (s.unop.len + 1)).obj ⟨s, Nat.lt_succ_self _⟩

/-- Any truncation containing the object gives the same object. -/
theorem diagramTowerObjEq (s : SimplexCategoryᵒᵖ) {k : ℕ} (hs : s.unop.len < k) :
    (T.stage k).obj ⟨s, hs⟩ = diagramTowerObj T s :=
  CategoryTheory.Functor.congr_obj (diagramTower_restrict T (Nat.succ_le_of_lt hs))
    ⟨s, Nat.lt_succ_self _⟩

/-- Use any truncation containing both endpoints to act on a simplex operator. -/
def diagramTowerMapAt {s t : SimplexCategoryᵒᵖ} (f : s ⟶ t) {k : ℕ}
    (hs : s.unop.len < k) (ht : t.unop.len < k) :
    diagramTowerObj T s ⟶ diagramTowerObj T t :=
  eqToHom (diagramTowerObjEq T s hs).symm ≫
    (T.stage k).map (ObjectProperty.homMk
      (X := (⟨s, hs⟩ : BelowDegree k)) (Y := (⟨t, ht⟩ : BelowDegree k)) f) ≫
    eqToHom (diagramTowerObjEq T t ht)

theorem diagramTowerMapAt_eq_of_le {s t : SimplexCategoryᵒᵖ} (f : s ⟶ t) {j k : ℕ}
    (hs : s.unop.len < j) (ht : t.unop.len < j) (h : j ≤ k) :
    diagramTowerMapAt T f (lt_of_lt_of_le hs h) (lt_of_lt_of_le ht h) =
      diagramTowerMapAt T f hs ht := by
  let g : (⟨s, hs⟩ : BelowDegree j) ⟶ (⟨t, ht⟩ : BelowDegree j) :=
    ObjectProperty.homMk f
  have w := CategoryTheory.Functor.congr_hom (diagramTower_restrict T h) g
  unfold diagramTowerMapAt
  change (T.stage k).map (ObjectProperty.homMk
      (X := (⟨s, lt_of_lt_of_le hs h⟩ : BelowDegree k))
      (Y := (⟨t, lt_of_lt_of_le ht h⟩ : BelowDegree k)) f) = _ at w
  rw [w]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rfl

theorem diagramTowerMapAt_id (s : SimplexCategoryᵒᵖ) {k : ℕ} (hs : s.unop.len < k) :
    diagramTowerMapAt T (𝟙 s) hs hs = 𝟙 _ := by
  unfold diagramTowerMapAt
  change eqToHom _ ≫ (T.stage k).map (𝟙 (⟨s, hs⟩ : BelowDegree k)) ≫ eqToHom _ = _
  rw [(T.stage k).map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

theorem diagramTowerMapAt_comp {s t u : SimplexCategoryᵒᵖ} (f : s ⟶ t) (g : t ⟶ u)
    {k : ℕ} (hs : s.unop.len < k) (ht : t.unop.len < k) (hu : u.unop.len < k) :
    diagramTowerMapAt T (f ≫ g) hs hu =
      diagramTowerMapAt T f hs ht ≫ diagramTowerMapAt T g ht hu := by
  simp only [diagramTowerMapAt, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← (T.stage k).map_comp_assoc]
  rfl

/-- The full simplicial diagram obtained by gluing the truncations. -/
def glueDiagramTower : SimplexCategoryᵒᵖ ⥤ C where
  obj := diagramTowerObj T
  map {s t} f := diagramTowerMapAt T f (Nat.lt_succ_of_le (le_max_left _ _))
    (Nat.lt_succ_of_le (le_max_right _ _))
  map_id s := diagramTowerMapAt_id T s _
  map_comp {s t u} f g := by
    let N := max (max s.unop.len t.unop.len) u.unop.len + 1
    have h₁ : max s.unop.len u.unop.len + 1 ≤ N := by omega
    have h₂ : max s.unop.len t.unop.len + 1 ≤ N := by omega
    have h₃ : max t.unop.len u.unop.len + 1 ≤ N := by omega
    rw [← diagramTowerMapAt_eq_of_le T (f ≫ g) _ _ h₁,
      ← diagramTowerMapAt_eq_of_le T f _ _ h₂, ← diagramTowerMapAt_eq_of_le T g _ _ h₃]
    exact diagramTowerMapAt_comp T f g _ _ _

/-- The glued diagram restricts to each given stage. -/
theorem glueDiagramTower_restrict (k : ℕ) :
    lowerDiagram k (glueDiagramTower T) = T.stage k := by
  refine CategoryTheory.Functor.ext (fun s ↦ (diagramTowerObjEq T s.obj s.property).symm) ?_
  intro s t f
  have h : max s.obj.unop.len t.obj.unop.len + 1 ≤ k := by
    have hs : s.obj.unop.len < k := s.property
    have ht : t.obj.unop.len < k := t.property
    omega
  change diagramTowerMapAt T f.hom _ _ =
    eqToHom (diagramTowerObjEq T s.obj s.property).symm ≫ (T.stage k).map f ≫
      eqToHom (diagramTowerObjEq T t.obj t.property)
  rw [← diagramTowerMapAt_eq_of_le T f.hom _ _ h]
  rfl

end DaggerModels.PartII
