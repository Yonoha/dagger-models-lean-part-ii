import DaggerModelsPartII.JTHigherInterleavedOperators
import DaggerModelsPartII.JTParametricRelativeExtension

/-!
# Interleaved coefficient extensions of exact fixed-square families
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFixedLiftSpaceInterleaved

open JTHigherInterleavedParameter

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

variable {A X Y : SSet.{u}} {k : SimplexCategory} {i : A ⟶ simplex k}
variable {t : A ⟶ X} {p : X ⟶ Y} {b : simplex k ⟶ Y}

/-- An entire extension to the larger ordered coefficient, with exact
base and stationary equations. -/
@[ext]
structure Extension (sq : CommSq t i p b) (n : SimplexCategory) where
  map : simplex (common k n) ⟶ X
  stationary : (i ▷ simplex n) ≫ prism k n ≫ map = fst A (simplex n) ≫ t
  over : map ≫ p = SSet.stdSimplex.map (ret k n) ≫ b

variable (sq : CommSq t i p b)

theorem prism_over {n : SimplexCategory} (E : Extension sq n) :
    (prism k n ≫ E.map) ≫ p = fst (simplex k) (simplex n) ≫ b := by
  rw [Category.assoc, E.over, ← Category.assoc, prism_ret]

/-- Extend the whole fixed-square family along the actual prism trivial
cofibration. Both original fixed-square equations are retained. -/
theorem exists_extension (n : SimplexCategory) [Fibration p]
    (f : simplex k ⊗ simplex n ⟶ X)
    (hf : f ≫ p = fst (simplex k) (simplex n) ≫ b)
    (ht : (i ▷ simplex n) ≫ f = fst A (simplex n) ≫ t) :
    ∃ E : Extension sq n, prism k n ≫ E.map = f := by
  letI : Cofibration (prism.{u} k n) := SSet.modelCategoryQuillen.cofibration_of_mono _
  letI := prism_weak.{u} k n
  let c : CommSq f (prism k n) p (SSet.stdSimplex.map (ret k n) ≫ b) :=
    ⟨by rw [hf, ← Category.assoc, prism_ret]⟩
  exact ⟨⟨c.lift, by rw [c.fac_left, ht], c.fac_right⟩, c.fac_left⟩

/-- Precompose with the original interleaved time operator. -/
def restrict {m n : SimplexCategory} (j : m ⟶ n) (E : Extension sq n) : Extension sq m where
  map := SSet.stdSimplex.map (mapTime k j) ≫ E.map
  stationary := by
    rw [← Category.assoc (prism k m), prism_mapTime, Category.assoc,
      ← whisker_exchange_assoc, E.stationary, whiskerLeft_fst_assoc]
  over := by
    rw [Category.assoc, E.over, ← Category.assoc, ← SSet.stdSimplex.map_comp, mapTime_ret]

theorem restrict_id {n : SimplexCategory} (E : Extension sq n) :
    restrict sq (𝟙 n) E = E := by
  apply Extension.ext
  change SSet.stdSimplex.map (mapTime k (𝟙 n)) ≫ E.map = E.map
  rw [mapTime_id, SSet.stdSimplex.{u}.map_id, Category.id_comp]

theorem restrict_comp {l m n : SimplexCategory} (j : l ⟶ m) (j' : m ⟶ n) (E : Extension sq n) :
    restrict sq (j ≫ j') E = restrict sq j (restrict sq j' E) := by
  apply Extension.ext
  change SSet.stdSimplex.map (mapTime k (j ≫ j')) ≫ E.map =
    SSet.stdSimplex.map (mapTime k j) ≫ SSet.stdSimplex.map (mapTime k j') ≫ E.map
  rw [mapTime_comp, SSet.stdSimplex.{u}.map_comp, Category.assoc]

/-- The full space of enlargement choices, with strict faces and degeneracies. -/
def extensionSpace : SSet.{u} where
  obj n := Extension sq n.unop
  map j := restrict sq j.unop
  map_id n := by
    funext E
    exact restrict_id sq E
  map_comp j j' := by
    funext E
    exact restrict_comp sq j'.unop j.unop E

/-- The projection to the original entire product prism commutes with
every time operator. -/
theorem restrict_prism {m n : SimplexCategory} (j : m ⟶ n) (E : Extension sq n) :
    prism k m ≫ (restrict sq j E).map =
      (simplex k ◁ SSet.stdSimplex.map j) ≫ prism k n ≫ E.map := by
  change prism k m ≫ SSet.stdSimplex.map (mapTime k j) ≫ E.map = _
  rw [← Category.assoc, prism_mapTime, Category.assoc]

end

end DaggerModels.PartII.JTFixedLiftSpaceInterleaved
