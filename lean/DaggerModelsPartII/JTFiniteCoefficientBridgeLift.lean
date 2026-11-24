import DaggerModelsPartII.JTFiniteCoefficientBridgeOverlap
import DaggerModelsPartII.JTDisjointPrismExtension
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv

/-!
# Simultaneous lifts over a finite family of coefficient orders
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeLift

open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgePrism JTFiniteCoefficientBridgeOverlap
open JTFixedLiftSpaceTimeEquiv
open SSet.Subcomplex

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{v}.obj k

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
variable (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory)

private abbrev common := JTHigherInterleavedParameter.common
private abbrev sideMap (e : Fin (m + 1)) := SSet.stdSimplex.{v}.map (side c u h hu n e)
private abbrev sidePrism (e : Fin (m + 1)) := JTCommonCoefficientParameter.prism.{v} (c e) n

variable {A X Y : SSet.{v}} {i : A ⟶ simplex k} {p : X ⟶ Y}
variable [Fibration p] {t : A ⟶ X}
variable (g : simplex b' ⟶ Y) (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
variable (E : (e : Fin (m + 1)) → simplex (common k n) ⟶ X)
variable (hbase : ∀ e, E e ≫ p = sideMap c u h hu n e ≫ SSet.stdSimplex.map (base c u n) ≫ g)

include hbase in
/-- The relative extension retains a prescribed entire normalization prism
as well as every supplied ordered side. -/
theorem exists_relative_extension
    (x : (SSet.ihomToPullbackFiber sq).obj (op (time m n)))
    (hx : ∀ e, (simplex k ◁ SSet.stdSimplex.map (timeSide n e)) ≫ timeMap sq (time m n) x =
      sidePrism c n e ≫ E e) :
    ∃ L : simplex (bridge k n m) ⟶ X,
      prism c u n ≫ L = timeMap sq (time m n) x ∧
      (∀ e, sideMap c u h hu n e ≫ L = E e) ∧
      L ≫ p = SSet.stdSimplex.map (base c u n) ≫ g := by
  let f := prism.{v} c u n
  let j := sideMap.{v} c u h hu n
  let V := timeMap sq (time m n) x
  let q := SSet.stdSimplex.map (base c u n) ≫ g
  haveI := prism_weak.{v} c u n
  haveI (e : Fin (m + 1)) : Mono (j e) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono _
  have hv : V ≫ p = f ≫ q := by
    change timeMap sq (time m n) x ≫ p =
      prism c u n ≫ SSet.stdSimplex.map (base c u n) ≫ g
    rw [(timeMap_conditions sq (time m n) x).2, ← Category.assoc (prism c u n),
      prism_base, Category.assoc]
  apply JTDisjointPrismExtension.exists_extension f j (side_disjoint c u h hu n)
    (sideComparison_weak c u h hu n) q V E hv hbase
  intro e
  apply (cancel_epi (sidePreimageIso c u h hu n e).hom).1
  rw [← Category.assoc, sidePreimageIso_ι, hx]
  symm
  calc
    _ = ((sidePreimageIso c u h hu n e).hom ≫ (range (j e)).fromPreimage f) ≫
        inv (toRange (j e)) ≫ E e := by rw [Category.assoc]
    _ = _ := by
      dsimp only [f, j]
      rw [sidePreimageIso_compare, Category.assoc, IsIso.hom_inv_id_assoc]

variable [Mono i] [WeakEquivalence i]

include sq hbase in
/-- All independently supplied sides extend with one base map and the
full stationary equation on the joining ordinary prism. -/
theorem exists_extension
    (hstat : ∀ e, (i ▷ simplex n) ≫ sidePrism c n e ≫ E e = fst A (simplex n) ≫ t) :
    ∃ L : simplex (bridge k n m) ⟶ X,
      (∀ e, sideMap c u h hu n e ≫ L = E e) ∧
      L ≫ p = SSet.stdSimplex.map (base c u n) ≫ g ∧
      (i ▷ simplex (time m n)) ≫ prism c u n ≫ L = fst A (simplex (time m n)) ≫ t := by
  have sideBase (e : Fin (m + 1)) :
      sidePrism c n e ≫ sideMap c u h hu n e ≫ SSet.stdSimplex.map (base c u n) ≫ g =
        fst (simplex k) (simplex n) ≫ SSet.stdSimplex.map u ≫ g := by
    rw [← Category.assoc, ← prism_side, Category.assoc]
    rw [← Category.assoc (prism c u n), prism_base, Category.assoc, whiskerLeft_fst_assoc]
  let v (e : Fin (m + 1)) : TimeLift sq n :=
    ⟨sidePrism c n e ≫ E e, hstat e, by rw [Category.assoc, hbase]; exact sideBase e⟩
  obtain ⟨x, hx⟩ := fixedSquare_exists_join sq m n (fun e ↦ (timeEquiv sq n).symm (v e))
  have H (e : Fin (m + 1)) :
      (simplex k ◁ SSet.stdSimplex.map (timeSide n e)) ≫ timeMap sq (time m n) x =
        sidePrism c n e ≫ E e := by
    rw [← timeMap_map sq (timeSide n e) x, hx, ← timeEquiv_apply_val, Equiv.apply_symm_apply]
  obtain ⟨L, hL, hSide, hBase⟩ :=
    exists_relative_extension c u h hu n g sq E hbase x H
  refine ⟨L, hSide, hBase, ?_⟩
  rw [hL]
  exact (timeMap_conditions sq (time m n) x).1

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeLift
