import DaggerModelsPartII.ReedySeededFactorization

/-! Global maps of the Reedy factorization extending a prescribed first stage. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y)
  (P Q : MorphismProperty C) [HasFactorization P Q]
  (seed : ReedyFactorizationBelow f 1)

def seededReedyLeftApp (s : SimplexCategoryᵒᵖ) :
    X.obj s ⟶ (seededReedyMid f P Q seed).obj s :=
  (seededReedyBelow f P Q seed (s.unop.len + 1)).left.app ⟨s, Nat.lt_succ_self _⟩

def seededReedyRightApp (s : SimplexCategoryᵒᵖ) :
    (seededReedyMid f P Q seed).obj s ⟶ Y.obj s :=
  (seededReedyBelow f P Q seed (s.unop.len + 1)).right.app ⟨s, Nat.lt_succ_self _⟩

theorem seededReedyLeftApp_eq_at (s : SimplexCategoryᵒᵖ) {k : ℕ}
    (hs : s.unop.len < k) :
    seededReedyLeftApp f P Q seed s =
      (seededReedyBelow f P Q seed k).left.app ⟨s, hs⟩ ≫
        eqToHom (diagramTowerObjEq (seededReedyTower f P Q seed) s hs) := by
  rw [show (seededReedyBelow f P Q seed k).left.app ⟨s, hs⟩ = _ from
    seededReedyLeft_stable f P Q seed (Nat.succ_le_of_lt hs)
      ⟨s, Nat.lt_succ_self _⟩]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

theorem seededReedyRightApp_eq_at (s : SimplexCategoryᵒᵖ) {k : ℕ}
    (hs : s.unop.len < k) :
    seededReedyRightApp f P Q seed s =
      eqToHom (diagramTowerObjEq (seededReedyTower f P Q seed) s hs).symm ≫
        (seededReedyBelow f P Q seed k).right.app ⟨s, hs⟩ := by
  rw [show (seededReedyBelow f P Q seed k).right.app ⟨s, hs⟩ = _ from
    seededReedyRight_stable f P Q seed (Nat.succ_le_of_lt hs)
      ⟨s, Nat.lt_succ_self _⟩]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- The left factor on the full simplicial diagram, retaining the supplied
degree-zero component. -/
def seededReedyLeft : X ⟶ seededReedyMid f P Q seed where
  app := seededReedyLeftApp f P Q seed
  naturality s t g := by
    let N := max s.unop.len t.unop.len + 1
    have hs : s.unop.len < N := Nat.lt_succ_of_le (le_max_left _ _)
    have ht : t.unop.len < N := Nat.lt_succ_of_le (le_max_right _ _)
    let g' : (⟨s, hs⟩ : BelowDegree N) ⟶ (⟨t, ht⟩ : BelowDegree N) := ObjectProperty.homMk g
    let F := seededReedyBelow f P Q seed N
    rw [seededReedyLeftApp_eq_at f P Q seed s hs,
      seededReedyLeftApp_eq_at f P Q seed t ht]
    change X.map g ≫ F.left.app ⟨t, ht⟩ ≫
        eqToHom (diagramTowerObjEq (seededReedyTower f P Q seed) t ht) =
      (F.left.app ⟨s, hs⟩ ≫
        eqToHom (diagramTowerObjEq (seededReedyTower f P Q seed) s hs)) ≫
        diagramTowerMapAt (seededReedyTower f P Q seed) g hs ht
    simp only [diagramTowerMapAt, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (X.map g), ← Category.assoc (F.left.app ⟨s, hs⟩)]
    exact congrArg (fun k ↦ k ≫ eqToHom
      (diagramTowerObjEq (seededReedyTower f P Q seed) t ht)) (F.left.naturality g')

/-- The right factor on the full simplicial diagram, retaining the supplied
degree-zero component. -/
def seededReedyRight : seededReedyMid f P Q seed ⟶ Y where
  app := seededReedyRightApp f P Q seed
  naturality s t g := by
    let N := max s.unop.len t.unop.len + 1
    have hs : s.unop.len < N := Nat.lt_succ_of_le (le_max_left _ _)
    have ht : t.unop.len < N := Nat.lt_succ_of_le (le_max_right _ _)
    let g' : (⟨s, hs⟩ : BelowDegree N) ⟶ (⟨t, ht⟩ : BelowDegree N) := ObjectProperty.homMk g
    let F := seededReedyBelow f P Q seed N
    rw [seededReedyRightApp_eq_at f P Q seed s hs,
      seededReedyRightApp_eq_at f P Q seed t ht]
    change diagramTowerMapAt (seededReedyTower f P Q seed) g hs ht ≫
        eqToHom (diagramTowerObjEq (seededReedyTower f P Q seed) t ht).symm ≫
        F.right.app ⟨t, ht⟩ =
      (eqToHom (diagramTowerObjEq (seededReedyTower f P Q seed) s hs).symm ≫
        F.right.app ⟨s, hs⟩) ≫ Y.map g
    simp only [diagramTowerMapAt, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    exact congrArg (fun k ↦ eqToHom
      (diagramTowerObjEq (seededReedyTower f P Q seed) s hs).symm ≫ k)
        (F.right.naturality g')

/-- The two global factors compose to the given map. -/
theorem seededReedy_fac :
    seededReedyLeft f P Q seed ≫ seededReedyRight f P Q seed = f := by
  ext s
  exact NatTrans.congr_app (seededReedyBelow f P Q seed (s.unop.len + 1)).fac
    ⟨s, Nat.lt_succ_self _⟩

/-- The left factor agrees literally with the seed in degree zero. -/
theorem seededReedyLeft_app_zero :
    (seededReedyLeft f P Q seed).app (op ⦋0⦌) =
      seed.left.app ⟨op ⦋0⦌, by change (0 : ℕ) < 1; decide⟩ := rfl

/-- The right factor agrees literally with the seed in degree zero. -/
theorem seededReedyRight_app_zero :
    (seededReedyRight f P Q seed).app (op ⦋0⦌) =
      seed.right.app ⟨op ⦋0⦌, by change (0 : ℕ) < 1; decide⟩ := rfl

end

end DaggerModels.PartII
