import DaggerModelsPartII.ReedyFactorizationBelow
import DaggerModelsPartII.ReedyGlueTruncations

/-! Glue the compatible degree-by-degree factorizations to a factorization of simplicial maps. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y)
  (P Q : MorphismProperty C) [HasFactorization P Q]

/-- The compatible family of intermediate truncations. -/
def reedyFactorizationTower : DiagramTower C where
  stage n := (reedyFactorizationBelow f P Q n).mid
  step n := (chooseReedyFactorizationDegree
    (prev := reedyFactorizationBelow f P Q n) P Q).next_restrict

theorem reedyFactorizationLeft_stable {j k : ℕ} (h : j ≤ k) (s : BelowDegree j) :
    (reedyFactorizationBelow f P Q k).left.app ((belowDegreeInclusion h).obj s) =
      (reedyFactorizationBelow f P Q j).left.app s ≫
        eqToHom (CategoryTheory.Functor.congr_obj
          (diagramTower_restrict (reedyFactorizationTower f P Q) h) s).symm := by
  induction h with
  | refl =>
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  | @step k h ih =>
    let D := chooseReedyFactorizationDegree (prev := reedyFactorizationBelow f P Q k) P Q
    change D.next.left.app ((belowDegreeInclusion (Nat.le_succ k)).obj
      ((belowDegreeInclusion h).obj s)) = _
    rw [D.next_left_app_old, ih]
    simp only [Category.assoc, eqToHom_trans]

theorem reedyFactorizationRight_stable {j k : ℕ} (h : j ≤ k) (s : BelowDegree j) :
    (reedyFactorizationBelow f P Q k).right.app ((belowDegreeInclusion h).obj s) =
      eqToHom (CategoryTheory.Functor.congr_obj
        (diagramTower_restrict (reedyFactorizationTower f P Q) h) s) ≫
      (reedyFactorizationBelow f P Q j).right.app s := by
  induction h with
  | refl =>
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  | @step k h ih =>
    let D := chooseReedyFactorizationDegree (prev := reedyFactorizationBelow f P Q k) P Q
    change D.next.right.app ((belowDegreeInclusion (Nat.le_succ k)).obj
      ((belowDegreeInclusion h).obj s)) = _
    rw [D.next_right_app_old, ih]
    simp only [eqToHom_trans_assoc]

/-- The intermediate diagram on all degrees. -/
def reedyFactorizationMid : SimplexCategoryᵒᵖ ⥤ C :=
  glueDiagramTower (reedyFactorizationTower f P Q)

def reedyFactorizationLeftApp (s : SimplexCategoryᵒᵖ) :
    X.obj s ⟶ (reedyFactorizationMid f P Q).obj s :=
  (reedyFactorizationBelow f P Q (s.unop.len + 1)).left.app ⟨s, Nat.lt_succ_self _⟩

def reedyFactorizationRightApp (s : SimplexCategoryᵒᵖ) :
    (reedyFactorizationMid f P Q).obj s ⟶ Y.obj s :=
  (reedyFactorizationBelow f P Q (s.unop.len + 1)).right.app ⟨s, Nat.lt_succ_self _⟩

theorem reedyFactorizationLeftApp_eq_at (s : SimplexCategoryᵒᵖ) {k : ℕ} (hs : s.unop.len < k) :
    reedyFactorizationLeftApp f P Q s =
      (reedyFactorizationBelow f P Q k).left.app ⟨s, hs⟩ ≫
        eqToHom (diagramTowerObjEq (reedyFactorizationTower f P Q) s hs) := by
  rw [show (reedyFactorizationBelow f P Q k).left.app ⟨s, hs⟩ = _ from
    reedyFactorizationLeft_stable f P Q (Nat.succ_le_of_lt hs) ⟨s, Nat.lt_succ_self _⟩]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

theorem reedyFactorizationRightApp_eq_at (s : SimplexCategoryᵒᵖ) {k : ℕ} (hs : s.unop.len < k) :
    reedyFactorizationRightApp f P Q s =
      eqToHom (diagramTowerObjEq (reedyFactorizationTower f P Q) s hs).symm ≫
        (reedyFactorizationBelow f P Q k).right.app ⟨s, hs⟩ := by
  rw [show (reedyFactorizationBelow f P Q k).right.app ⟨s, hs⟩ = _ from
    reedyFactorizationRight_stable f P Q (Nat.succ_le_of_lt hs) ⟨s, Nat.lt_succ_self _⟩]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- The left factor on all degrees. -/
def reedyFactorizationLeft : X ⟶ reedyFactorizationMid f P Q where
  app := reedyFactorizationLeftApp f P Q
  naturality s t g := by
    let N := max s.unop.len t.unop.len + 1
    have hs : s.unop.len < N := Nat.lt_succ_of_le (le_max_left _ _)
    have ht : t.unop.len < N := Nat.lt_succ_of_le (le_max_right _ _)
    let g' : (⟨s, hs⟩ : BelowDegree N) ⟶ (⟨t, ht⟩ : BelowDegree N) := ObjectProperty.homMk g
    let F := reedyFactorizationBelow f P Q N
    rw [reedyFactorizationLeftApp_eq_at f P Q s hs, reedyFactorizationLeftApp_eq_at f P Q t ht]
    change X.map g ≫ F.left.app ⟨t, ht⟩ ≫
        eqToHom (diagramTowerObjEq (reedyFactorizationTower f P Q) t ht) =
      (F.left.app ⟨s, hs⟩ ≫ eqToHom (diagramTowerObjEq (reedyFactorizationTower f P Q) s hs)) ≫
        diagramTowerMapAt (reedyFactorizationTower f P Q) g hs ht
    simp only [diagramTowerMapAt, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [← Category.assoc (X.map g), ← Category.assoc (F.left.app ⟨s, hs⟩)]
    exact congrArg (fun k ↦ k ≫ eqToHom
      (diagramTowerObjEq (reedyFactorizationTower f P Q) t ht)) (F.left.naturality g')

/-- The right factor on all degrees. -/
def reedyFactorizationRight : reedyFactorizationMid f P Q ⟶ Y where
  app := reedyFactorizationRightApp f P Q
  naturality s t g := by
    let N := max s.unop.len t.unop.len + 1
    have hs : s.unop.len < N := Nat.lt_succ_of_le (le_max_left _ _)
    have ht : t.unop.len < N := Nat.lt_succ_of_le (le_max_right _ _)
    let g' : (⟨s, hs⟩ : BelowDegree N) ⟶ (⟨t, ht⟩ : BelowDegree N) := ObjectProperty.homMk g
    let F := reedyFactorizationBelow f P Q N
    rw [reedyFactorizationRightApp_eq_at f P Q s hs, reedyFactorizationRightApp_eq_at f P Q t ht]
    change diagramTowerMapAt (reedyFactorizationTower f P Q) g hs ht ≫
        eqToHom (diagramTowerObjEq (reedyFactorizationTower f P Q) t ht).symm ≫
        F.right.app ⟨t, ht⟩ =
      (eqToHom (diagramTowerObjEq (reedyFactorizationTower f P Q) s hs).symm ≫
        F.right.app ⟨s, hs⟩) ≫ Y.map g
    simp only [diagramTowerMapAt, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    exact congrArg (fun k ↦ eqToHom
      (diagramTowerObjEq (reedyFactorizationTower f P Q) s hs).symm ≫ k) (F.right.naturality g')

/-- The glued maps give a factorization of the original simplicial map. -/
theorem reedyFactorization_fac :
    reedyFactorizationLeft f P Q ≫ reedyFactorizationRight f P Q = f := by
  ext s
  exact NatTrans.congr_app (reedyFactorizationBelow f P Q (s.unop.len + 1)).fac
    ⟨s, Nat.lt_succ_self _⟩

end

end DaggerModels.PartII
