import DaggerModelsPartII.ReedyFactorization

/-!
# Reedy factorization from a prescribed first degree

The degree-one truncation is supplied by the caller. Subsequent degrees use
the retained relative Reedy factorization step. In particular, a caller can
place an identity factorization in degree zero before this generic extension.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y)
  (P Q : MorphismProperty C) [HasFactorization P Q]

/-- Extend a prescribed degree-zero factorization through all positive
truncations. Stage `0` here means the truncation containing degree zero. -/
def seededReedyAbove (seed : ReedyFactorizationBelow f 1) :
    (n : ℕ) → ReedyFactorizationBelow f (n + 1)
  | 0 => seed
  | n + 1 => (chooseReedyFactorizationDegree
      (prev := seededReedyAbove seed n) P Q).next

@[simp] theorem seededReedyAbove_zero (seed : ReedyFactorizationBelow f 1) :
    seededReedyAbove f P Q seed 0 = seed := rfl

/-- Add the empty truncation to the prescribed positive tower. -/
def seededReedyBelow (seed : ReedyFactorizationBelow f 1) :
    (n : ℕ) → ReedyFactorizationBelow f n
  | 0 => ⟨lowerDiagram 0 X, 𝟙 _,
      CategoryTheory.Functor.whiskerLeft (belowDegree 0).ι f,
      Category.id_comp _⟩
  | n + 1 => seededReedyAbove f P Q seed n

@[simp] theorem seededReedyBelow_one (seed : ReedyFactorizationBelow f 1) :
    seededReedyBelow f P Q seed 1 = seed := rfl

/-- Every extension after the prescribed seed is the existing Reedy degree
step, with its unchanged relative factorization properties. -/
theorem seededReedyBelow_succ_succ (seed : ReedyFactorizationBelow f 1)
    (n : ℕ) :
    seededReedyBelow f P Q seed (n + 2) =
      (chooseReedyFactorizationDegree
        (prev := seededReedyBelow f P Q seed (n + 1)) P Q).next := rfl

/-- The seeded compatible family of intermediate truncations. -/
def seededReedyTower (seed : ReedyFactorizationBelow f 1) : DiagramTower C where
  stage n := (seededReedyBelow f P Q seed n).mid
  step
    | 0 => by
        apply CategoryTheory.Functor.ext
        · intro s
          exact (Nat.not_lt_zero _ s.property).elim
        · intro s
          exact (Nat.not_lt_zero _ s.property).elim
    | n + 1 => (chooseReedyFactorizationDegree
        (prev := seededReedyBelow f P Q seed (n + 1)) P Q).next_restrict

@[simp] theorem seededReedyTower_stage_one (seed : ReedyFactorizationBelow f 1) :
    (seededReedyTower f P Q seed).stage 1 = seed.mid := rfl

/-- Every restriction of the seeded tower agrees with its earlier stage. -/
theorem seededReedyTower_restrict (seed : ReedyFactorizationBelow f 1)
    {j k : ℕ} (h : j ≤ k) :
    belowDegreeInclusion h ⋙ (seededReedyTower f P Q seed).stage k =
      (seededReedyTower f P Q seed).stage j :=
  diagramTower_restrict (seededReedyTower f P Q seed) h

/-- The seeded left factors agree whenever an older degree is viewed in a
larger truncation. -/
theorem seededReedyLeft_stable (seed : ReedyFactorizationBelow f 1)
    {j k : ℕ} (h : j ≤ k) (s : BelowDegree j) :
    (seededReedyBelow f P Q seed k).left.app ((belowDegreeInclusion h).obj s) =
      (seededReedyBelow f P Q seed j).left.app s ≫
        eqToHom (CategoryTheory.Functor.congr_obj
          (seededReedyTower_restrict f P Q seed h) s).symm := by
  induction h with
  | refl =>
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  | @step k h ih =>
    cases k with
    | zero =>
        have hj : j = 0 := Nat.eq_zero_of_le_zero h
        subst j
        exact (Nat.not_lt_zero _ s.property).elim
    | succ n =>
        let D := chooseReedyFactorizationDegree
          (prev := seededReedyBelow f P Q seed (n + 1)) P Q
        change D.next.left.app ((belowDegreeInclusion (Nat.le_succ (n + 1))).obj
          ((belowDegreeInclusion h).obj s)) = _
        rw [D.next_left_app_old, ih]
        simp only [Category.assoc, eqToHom_trans]

/-- The seeded right factors agree whenever an older degree is viewed in a
larger truncation. -/
theorem seededReedyRight_stable (seed : ReedyFactorizationBelow f 1)
    {j k : ℕ} (h : j ≤ k) (s : BelowDegree j) :
    (seededReedyBelow f P Q seed k).right.app ((belowDegreeInclusion h).obj s) =
      eqToHom (CategoryTheory.Functor.congr_obj
        (seededReedyTower_restrict f P Q seed h) s) ≫
      (seededReedyBelow f P Q seed j).right.app s := by
  induction h with
  | refl =>
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  | @step k h ih =>
    cases k with
    | zero =>
        have hj : j = 0 := Nat.eq_zero_of_le_zero h
        subst j
        exact (Nat.not_lt_zero _ s.property).elim
    | succ n =>
        let D := chooseReedyFactorizationDegree
          (prev := seededReedyBelow f P Q seed (n + 1)) P Q
        change D.next.right.app ((belowDegreeInclusion (Nat.le_succ (n + 1))).obj
          ((belowDegreeInclusion h).obj s)) = _
        rw [D.next_right_app_old, ih]
        simp only [eqToHom_trans_assoc]

/-- The glued intermediate object keeps the prescribed first truncation. -/
def seededReedyMid (seed : ReedyFactorizationBelow f 1) :
    SimplexCategoryᵒᵖ ⥤ C :=
  glueDiagramTower (seededReedyTower f P Q seed)

theorem seededReedyMid_restrict_one (seed : ReedyFactorizationBelow f 1) :
    lowerDiagram 1 (seededReedyMid f P Q seed) = seed.mid := by
  rw [seededReedyMid, glueDiagramTower_restrict]
  rfl

/-- In particular, the glued middle object is the prescribed one in degree zero. -/
theorem seededReedyMid_obj_zero (seed : ReedyFactorizationBelow f 1) :
    (seededReedyMid f P Q seed).obj (op ⦋0⦌) =
      seed.mid.obj ⟨op ⦋0⦌, by change (0 : ℕ) < 1; decide⟩ := rfl

end

end DaggerModels.PartII
