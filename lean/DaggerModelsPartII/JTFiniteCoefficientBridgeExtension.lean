import DaggerModelsPartII.JTFiniteCoefficientBridgeLift
import DaggerModelsPartII.JTCommonCoefficientLiftChoices

/-!
# Exact extensions on the finite coefficient bridge
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeExtension

open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgePrism JTFixedLiftSpaceTimeEquiv
open JTHigherInterleavedParameter (common)

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{v}.obj k

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable {A X Y : SSet.{v}} {i : A ⟶ simplex k} {t : A ⟶ X} {p : X ⟶ Y}
variable {g : simplex b' ⟶ Y}

/-- An exact extension on the entire finite bridge retains the complete
stationary and base equations. -/
@[ext] structure Extension (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    (n : SimplexCategory) where
  map : simplex (bridge k n m) ⟶ X
  stationary : (i ▷ simplex (time m n)) ≫ prism c u n ≫ map =
    fst A (simplex (time m n)) ≫ t
  over : map ≫ p = SSet.stdSimplex.map (base c u n) ≫ g

theorem prism_over (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    {n : SimplexCategory} (E : Extension c u sq n) :
    (prism c u n ≫ E.map) ≫ p =
      fst (simplex k) (simplex (time m n)) ≫ (SSet.stdSimplex.map u ≫ g) := by
  rw [Category.assoc, E.over, ← Category.assoc (prism c u n), prism_base, Category.assoc]

private def liftMap (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    {n : SimplexCategory} (E : Extension c u sq n) : TimeLift sq (time m n) :=
  ⟨prism c u n ≫ E.map, E.stationary, prism_over c u sq E⟩

/-- Forget the enlarged bridge while keeping its original normalization simplex. -/
def underlying (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    {n : SimplexCategory} (E : Extension c u sq n) :
    (SSet.ihomToPullbackFiber sq).obj (op (time m n)) :=
  (timeEquiv sq (time m n)).symm (liftMap c u sq E)

theorem underlying_timeMap (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    {n : SimplexCategory} (E : Extension c u sq n) :
    timeMap sq (time m n) (underlying c u sq E) = prism c u n ≫ E.map :=
  congrArg Subtype.val ((timeEquiv sq (time m n)).apply_symm_apply (liftMap c u sq E))

variable {m' : ℕ} {l : SimplexCategory}
variable {b₂ : Fin (m' + 1) → SimplexCategory}
variable {i' : A ⟶ simplex l} {u' : l ⟶ b'}

private theorem corner {n n' : SimplexCategory} (f : k ⟶ l)
    (j : time m n ⟶ time m' n')
    (hi : i ≫ SSet.stdSimplex.map f = i') :
    (i ▷ simplex (time m n)) ≫
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) =
        (A ◁ SSet.stdSimplex.map j) ≫ (i' ▷ simplex (time m' n')) := by
  simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hi]

/-- Abstract restriction along a prism square and an exact base square. -/
def restrict {n n' : SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), l ⟶ b₂ e)
    (u : k ⟶ b') (u' : l ⟶ b')
    (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    (sq' : CommSq t i' p (SSet.stdSimplex.map u' ≫ g))
    (f : k ⟶ l) (j : time m n ⟶ time m' n')
    (a : bridge k n m ⟶ bridge l n' m')
    (hprism : prism c u n ≫ SSet.stdSimplex.map a =
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) ≫ prism d u' n')
    (hbase : a ≫ base d u' n' = base c u n)
    (hi : i ≫ SSet.stdSimplex.map f = i')
    (E : Extension d u' sq' n') : Extension c u sq n where
  map := SSet.stdSimplex.map a ≫ E.map
  stationary := by
    calc
      _ = ((i ▷ simplex (time m n)) ≫
            (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j)) ≫
            prism d u' n' ≫ E.map := by
        rw [Category.assoc, ← Category.assoc (prism c u n), hprism, Category.assoc]
      _ = _ := by rw [corner f j hi, Category.assoc, E.stationary, whiskerLeft_fst_assoc]
  over := by
    rw [Category.assoc, E.over, ← Category.assoc, ← SSet.stdSimplex.map_comp, hbase]

theorem restrict_prism {n n' : SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), l ⟶ b₂ e)
    (u : k ⟶ b') (u' : l ⟶ b')
    (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    (sq' : CommSq t i' p (SSet.stdSimplex.map u' ≫ g))
    (f : k ⟶ l) (j : time m n ⟶ time m' n')
    (a : bridge k n m ⟶ bridge l n' m')
    (hprism : prism c u n ≫ SSet.stdSimplex.map a =
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) ≫ prism d u' n')
    (hbase : a ≫ base d u' n' = base c u n)
    (hi : i ≫ SSet.stdSimplex.map f = i')
    (E : Extension d u' sq' n') :
    prism c u n ≫ (restrict c d u u' sq sq' f j a hprism hbase hi E).map =
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) ≫ prism d u' n' ≫ E.map := by
  change prism c u n ≫ SSet.stdSimplex.map a ≫ E.map = _
  rw [← Category.assoc, hprism, Category.assoc]

private theorem base_precomp (u : k ⟶ b') (u' : l ⟶ b')
    (f : k ⟶ l) (hf : f ≫ u' = u) :
    SSet.stdSimplex.map f ≫ (SSet.stdSimplex.map u' ≫ g) =
      SSet.stdSimplex.map u ≫ g := by
  rw [← Category.assoc, ← SSet.stdSimplex.map_comp, hf]

/-- Restriction agrees with coefficient precomposition and time restriction
on the original normalization lift spaces. -/
theorem underlying_restrict {n n' : SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), l ⟶ b₂ e)
    (u : k ⟶ b') (u' : l ⟶ b')
    (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    (sq' : CommSq t i' p (SSet.stdSimplex.map u' ≫ g))
    (f : k ⟶ l) (hf : f ≫ u' = u)
    (j : time m n ⟶ time m' n')
    (a : bridge k n m ⟶ bridge l n' m')
    (hprism : prism c u n ≫ SSet.stdSimplex.map a =
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) ≫ prism d u' n')
    (hbase : a ≫ base d u' n' = base c u n)
    (hi : i ≫ SSet.stdSimplex.map f = i')
    (E : Extension d u' sq' n') :
    underlying c u sq (restrict c d u u' sq sq' f j a hprism hbase hi E) =
      (SSet.ihomToPullbackFiber sq : SSet.{v}).map j.op
        ((JTFixedLiftSpacePrecomp.precomp sq sq' (SSet.stdSimplex.map f) hi
          (base_precomp (g := g) u u' f hf)).app (op (time m' n'))
          (underlying d u' sq' E)) := by
  apply (timeEquiv sq (time m n)).injective
  apply Subtype.ext
  change timeMap sq (time m n)
    (underlying c u sq (restrict c d u u' sq sq' f j a hprism hbase hi E)) = _
  rw [underlying_timeMap, restrict_prism]
  have h := timeMap_map sq j
    ((JTFixedLiftSpacePrecomp.precomp sq sq' (SSet.stdSimplex.map f) hi
      (base_precomp (g := g) u u' f hf)).app (op (time m' n'))
      (underlying d u' sq' E))
  change _ = timeMap sq (time m n) _
  rw [h, timeMap_precomp, underlying_timeMap, ← Category.assoc (simplex k ◁ _),
    ← tensorHom_def']

/-- Package the relative finite bridge lift with its prescribed copies and
its exact original normalization simplex. -/
theorem exists_relative_extension [Fibration p]
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
    (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory)
    (g : simplex b' ⟶ Y)
    (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    (E : (e : Fin (m + 1)) → simplex (common k n) ⟶ X)
    (hbase : ∀ e, E e ≫ p =
      SSet.stdSimplex.map (side c u h hu n e) ≫
        SSet.stdSimplex.map (base c u n) ≫ g)
    (x : (SSet.ihomToPullbackFiber sq).obj (op (time m n)))
    (hx : ∀ e, (simplex k ◁ SSet.stdSimplex.map (timeSide n e)) ≫
      timeMap sq (time m n) x =
        JTCommonCoefficientParameter.prism (c e) n ≫ E e) :
    ∃ F : Extension c u sq n,
      (∀ e, SSet.stdSimplex.map (side c u h hu n e) ≫ F.map = E e) ∧
        underlying c u sq F = x := by
  obtain ⟨L, hL, hSide, hBase⟩ :=
    JTFiniteCoefficientBridgeLift.exists_relative_extension
      c u h hu n g sq E hbase x hx
  let F : Extension c u sq n :=
    { map := L
      stationary := by
        rw [hL]
        exact (timeMap_conditions sq (time m n) x).1
      over := hBase }
  refine ⟨F, hSide, ?_⟩
  apply (timeEquiv sq (time m n)).injective
  apply Subtype.ext
  change timeMap sq (time m n) (underlying c u sq F) = timeMap sq (time m n) x
  rw [underlying_timeMap, hL]

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeExtension
