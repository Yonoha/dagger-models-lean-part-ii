import DaggerModelsPartII.InjectiveKanModel
import DaggerModelsPartII.LeftProperPushoutComparison

/-!
# Gluing compatible weak covers of a simplicial diagram pushout

Factor one cover leg in the injective model before gluing. A common
parameter descends to the pushout, and the projection is levelwise weak.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTWeakCoveredPushout

noncomputable section

variable {I : Type} [SmallCategory I]

local instance : ModelCategory (I ⥤ SSet.{0}) := InjectiveKanDiagram.modelCategory I

variable {M X Y P M' X' Y' : I ⥤ SSet.{0}}
variable {a : M ⟶ X} {b : M ⟶ Y} {l : X ⟶ P} {r : Y ⟶ P}
variable (lower : IsPushout a b l r)
variable (a' : M' ⟶ X') (b' : M' ⟶ Y') (m : M' ⟶ M) (x : X' ⟶ X) (y : Y' ⟶ Y)
variable (ha : a' ≫ x = m ≫ a) (hb : b' ≫ y = m ≫ b)

private abbrev split :=
  factorizationData (cofibrations (I ⥤ SSet.{0})) (trivialFibrations (I ⥤ SSet.{0})) a'

/-- Glue the upper cover diagram after replacing its left leg by a monomorphism. -/
abbrev source := pushout (split a').i b'

include ha in
private theorem left_projects :
    (split a').i ≫ ((split a').p ≫ x) = m ≫ a := by
  rw [← Category.assoc, (split a').fac, ha]

include lower ha hb in
private theorem projections_agree :
    (split a').i ≫ (((split a').p ≫ x) ≫ l) = b' ≫ (y ≫ r) := by
  calc
    _ = m ≫ (a ≫ l) := by
      simpa only [Category.assoc] using congrArg (· ≫ l) (left_projects a' m x ha)
    _ = m ≫ (b ≫ r) := congrArg (m ≫ ·) lower.w
    _ = _ := by simpa only [Category.assoc] using (congrArg (· ≫ r) hb).symm

/-- The glued cover maps to the given original pushout. -/
def projection : source a' b' ⟶ P :=
  pushout.desc (((split a').p ≫ x) ≫ l) (y ≫ r) (projections_agree lower a' b' m x y ha hb)

@[reassoc]
theorem inl_projection :
    pushout.inl (split a').i b' ≫ projection lower a' b' m x y ha hb =
      ((split a').p ≫ x) ≫ l :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem inr_projection :
    pushout.inr (split a').i b' ≫ projection lower a' b' m x y ha hb = y ≫ r :=
  pushout.inr_desc _ _ _

/-- A shared parameter on the overlap gives a single parameter on the glued cover. -/
def parameter {Z : I ⥤ SSet.{0}} (s : X' ⟶ Z) (t : Y' ⟶ Z)
    (h : a' ≫ s = b' ≫ t) : source a' b' ⟶ Z :=
  pushout.desc ((split a').p ≫ s) t (by rw [← Category.assoc, (split a').fac, h])

@[reassoc]
theorem inl_parameter {Z : I ⥤ SSet.{0}} (s : X' ⟶ Z) (t : Y' ⟶ Z)
    (h : a' ≫ s = b' ≫ t) :
    pushout.inl (split a').i b' ≫ parameter a' b' s t h = (split a').p ≫ s :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem inr_parameter {Z : I ⥤ SSet.{0}} (s : X' ⟶ Z) (t : Y' ⟶ Z)
    (h : a' ≫ s = b' ≫ t) :
    pushout.inr (split a').i b' ≫ parameter a' b' s t h = t :=
  pushout.inr_desc _ _ _

/-- The glued projection is an objectwise Kan weak equivalence. -/
theorem projection_weak [Mono a]
    (hm : ∀ p, weakEquivalences SSet.{0} (m.app p))
    (hx : ∀ p, weakEquivalences SSet.{0} (x.app p))
    (hy : ∀ p, weakEquivalences SSet.{0} (y.app p)) (p : I) :
    weakEquivalences SSet.{0} ((projection lower a' b' m x y ha hb).app p) := by
  let D := I ⥤ SSet.{0}
  have mw : weakEquivalences D m := by
    rw [InjectiveKanDiagram.model_weakEquivalences I]
    exact hm
  have xw : weakEquivalences D x := by
    rw [InjectiveKanDiagram.model_weakEquivalences I]
    exact hx
  have yw : weakEquivalences D y := by
    rw [InjectiveKanDiagram.model_weakEquivalences I]
    exact hy
  have ac : cofibrations D a := by
    rw [InjectiveKanDiagram.model_cofibrations I]
    exact monomorphisms.infer_property a
  have pw : weakEquivalences D (split a').p :=
    (weakEquivalence_iff _).mp ((mem_trivialFibrations_iff _).mp (split a').hp).2
  have w := DaggerModels.PartII.weak_of_pushoutComparison
    (InjectiveKanDiagram.model_leftProper I) (IsPushout.of_hasPushout (split a').i b') lower
    (split a').hi ac m ((split a').p ≫ x) y (projection lower a' b' m x y ha hb)
    (left_projects a' m x ha) hb (inl_projection lower a' b' m x y ha hb)
    (inr_projection lower a' b' m x y ha hb) mw ((weakEquivalences D).comp_mem _ _ pw xw) yw
  have levelwise := (congrArg (fun A ↦ A (projection lower a' b' m x y ha hb))
     (InjectiveKanDiagram.model_weakEquivalences I)).mp w
  exact levelwise p

end

end DaggerModels.PartII.JTWeakCoveredPushout
