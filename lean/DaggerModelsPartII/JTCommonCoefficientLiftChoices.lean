import DaggerModelsPartII.JTCommonCoefficientPrism
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv

/-!
# Exact coefficient lift choices over a common base
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTCommonCoefficientLiftChoices

open JTCommonCoefficientParameter JTFixedLiftSpaceTimeEquiv

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{u}.obj a

variable {A X Y : SSet.{u}} {b k l : SimplexCategory} {c : k ⟶ b} {d : l ⟶ b}
variable {g : simplex b ⟶ Y} {t : A ⟶ X} {p : X ⟶ Y}
variable {i : A ⟶ simplex k} {i' : A ⟶ simplex l}
variable (sq : CommSq t i p (SSet.stdSimplex.map c ≫ g))

/-- A coefficient extension retains the stationary equation and the
chosen common-base map on the entire enlarged simplex. -/
@[ext] structure Extension (sq : CommSq t i p (SSet.stdSimplex.map c ≫ g))
    (n : SimplexCategory) where
  map : simplex (JTHigherInterleavedParameter.common k n) ⟶ X
  stationary : (i ▷ simplex n) ≫ prism c n ≫ map = fst A (simplex n) ≫ t
  over : map ≫ p = SSet.stdSimplex.map (base c n) ≫ g

theorem prism_over {n : SimplexCategory} (E : Extension sq n) :
    (prism c n ≫ E.map) ≫ p = fst (simplex k) (simplex n) ≫ (SSet.stdSimplex.map c ≫ g) := by
  rw [Category.assoc, E.over, ← Category.assoc, prism_base, Category.assoc]

private def liftMap {n : SimplexCategory} (E : Extension sq n) : TimeLift sq n :=
  ⟨prism c n ≫ E.map, E.stationary, prism_over sq E⟩

/-- Forget the enlargement and retain the original normalization simplex. -/
def underlying {n : SimplexCategory} (E : Extension sq n) :
    (SSet.ihomToPullbackFiber sq).obj (op n) :=
  (timeEquiv sq n).symm (liftMap sq E)

theorem underlying_timeMap {n : SimplexCategory} (E : Extension sq n) :
    timeMap sq n (underlying sq E) = prism c n ≫ E.map :=
  congrArg Subtype.val ((timeEquiv sq n).apply_symm_apply (liftMap sq E))

/-- Every exact prism simplex extends over the fixed common base. -/
theorem exists_extension [Fibration p] (n : SimplexCategory)
    (v : (SSet.ihomToPullbackFiber sq).obj (op n)) :
    ∃ E : Extension sq n, prism c n ≫ E.map = timeMap sq n v := by
  haveI := prism_weak.{u} c n
  haveI : Cofibration (prism.{u} c n) := SSet.modelCategoryQuillen.cofibration_of_mono _
  let L : CommSq (timeMap sq n v) (prism c n) p (SSet.stdSimplex.map (base c n) ≫ g) :=
    ⟨by rw [(timeMap_conditions sq n v).2, ← Category.assoc (prism c n), prism_base, Category.assoc]⟩
  exact ⟨⟨L.lift, by rw [L.fac_left]; exact (timeMap_conditions sq n v).1,
    L.fac_right⟩, L.fac_left⟩

variable (sq' : CommSq t i' p (SSet.stdSimplex.map d ≫ g))

private theorem corner {n m : SimplexCategory} (f : k ⟶ l) (j : n ⟶ m)
    (hi : i ≫ SSet.stdSimplex.map f = i') :
    (i ▷ simplex n) ≫ (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) =
      (A ◁ SSet.stdSimplex.map j) ≫ (i' ▷ simplex m) := by
  simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hi]

/-- Restriction along an arbitrary coefficient map over the common base
and an injective time map preserves the exact two equations. -/
def restrict {n m : SimplexCategory} (f : k ⟶ l) (hf : f ≫ d = c)
    (hi : i ≫ SSet.stdSimplex.map f = i')
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) (E : Extension sq' m) :
    Extension sq n where
  map := SSet.stdSimplex.map (JTCommonCoefficientParameter.map f hf j hj) ≫ E.map
  stationary := by
    calc
      _ = ((i ▷ simplex n) ≫ (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j)) ≫
          prism d m ≫ E.map := by
        rw [Category.assoc, ← Category.assoc (prism c n), prism_map f hf j hj, Category.assoc]
      _ = _ := by rw [corner f j hi, Category.assoc, E.stationary, whiskerLeft_fst_assoc]
  over := by
    rw [Category.assoc, E.over, ← Category.assoc, ← SSet.stdSimplex.map_comp, map_base]

theorem restrict_prism {n m : SimplexCategory} (f : k ⟶ l) (hf : f ≫ d = c)
    (hi : i ≫ SSet.stdSimplex.map f = i')
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) (E : Extension sq' m) :
    prism c n ≫ (restrict sq sq' f hf hi j hj E).map =
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) ≫ prism d m ≫ E.map := by
  change prism c n ≫ SSet.stdSimplex.map (JTCommonCoefficientParameter.map f hf j hj) ≫ E.map = _
  rw [← Category.assoc, prism_map, Category.assoc]

theorem base_precomp (f : k ⟶ l) (hf : f ≫ d = c) :
    SSet.stdSimplex.map f ≫ (SSet.stdSimplex.map d ≫ g) = SSet.stdSimplex.map c ≫ g := by
  rw [← Category.assoc, ← SSet.stdSimplex.map_comp, hf]

/-- On the original normalization space this is precisely the old
coefficient precomposition followed by the original time restriction. -/
theorem underlying_restrict {n m : SimplexCategory} (f : k ⟶ l) (hf : f ≫ d = c)
    (hi : i ≫ SSet.stdSimplex.map f = i')
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) (E : Extension sq' m) :
    underlying sq (restrict sq sq' f hf hi j hj E) =
      (SSet.ihomToPullbackFiber sq : SSet.{u}).map j.op
        ((JTFixedLiftSpacePrecomp.precomp sq sq' (SSet.stdSimplex.map f) hi
          (base_precomp (g := g) f hf)).app (op m) (underlying sq' E)) := by
  apply (timeEquiv sq n).injective
  apply Subtype.ext
  change timeMap sq n (underlying sq (restrict sq sq' f hf hi j hj E)) = _
  rw [underlying_timeMap, restrict_prism]
  have h := timeMap_map sq j ((JTFixedLiftSpacePrecomp.precomp sq sq'
    (SSet.stdSimplex.map f) hi (base_precomp (g := g) f hf)).app (op m) (underlying sq' E))
  change _ = timeMap sq n _
  rw [h, timeMap_precomp, underlying_timeMap, ← Category.assoc (simplex k ◁ _),
    ← tensorHom_def']

theorem restrict_id {n : SimplexCategory} (E : Extension sq n) :
    restrict sq sq (𝟙 k) (Category.id_comp c) (by rw [SSet.stdSimplex.{u}.map_id k, Category.comp_id])
      (𝟙 n) (fun _ _ h ↦ h) E = E := by
  apply Extension.ext
  change SSet.stdSimplex.map (JTCommonCoefficientParameter.map (𝟙 k) (Category.id_comp c)
    (𝟙 n) (fun _ _ h ↦ h)) ≫ E.map = _
  rw [map_id, SSet.stdSimplex.{u}.map_id, Category.id_comp]

/-- Coherent restriction uses the same original composite coefficient
and time operators. -/
theorem restrict_comp {l' n m m' : SimplexCategory} {e : l' ⟶ b}
    {i'' : A ⟶ simplex l'}
    (sq'' : CommSq t i'' p (SSet.stdSimplex.map e ≫ g))
    (f : k ⟶ l) (f' : l ⟶ l') (hf : f ≫ d = c) (hf' : f' ≫ e = d)
    (hi : i ≫ SSet.stdSimplex.map f = i') (hi' : i' ≫ SSet.stdSimplex.map f' = i'')
    (j : n ⟶ m) (j' : m ⟶ m') (hj : Function.Injective j.toOrderHom)
    (hj' : Function.Injective j'.toOrderHom) (E : Extension sq'' m') :
    restrict sq sq'' (f ≫ f') (by rw [Category.assoc, hf', hf])
      (by rw [SSet.stdSimplex.{u}.map_comp, ← Category.assoc, hi, hi'])
      (j ≫ j') (hj'.comp hj) E =
    restrict sq sq' f hf hi j hj (restrict sq' sq'' f' hf' hi' j' hj' E) := by
  apply Extension.ext
  change SSet.stdSimplex.map (JTCommonCoefficientParameter.map (f ≫ f') _
    (j ≫ j') (hj'.comp hj)) ≫ E.map =
    SSet.stdSimplex.map (JTCommonCoefficientParameter.map f hf j hj) ≫
      SSet.stdSimplex.map (JTCommonCoefficientParameter.map f' hf' j' hj') ≫ E.map
  rw [map_comp f f' hf hf' j j' hj hj', SSet.stdSimplex.{u}.map_comp, Category.assoc]

end

end DaggerModels.PartII.JTCommonCoefficientLiftChoices
