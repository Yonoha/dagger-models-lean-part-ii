import DaggerModelsPartII.JTFiniteCoefficientBridgeExtension

/-!
# Restriction of finite bridge extensions to their original sides
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeSideExtension

open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgePrism JTFixedLiftSpaceTimeEquiv

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{v}.obj a

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable {A X Y : SSet.{v}} {i : A ⟶ simplex k} {t : A ⟶ X} {p : X ⟶ Y}

/-- Restrict an exact bridge extension to one of its original coefficient sides. -/
def toSide (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (h : ∀ e, b e ⟶ b') (hu : ∀ e, c e ≫ h e = u)
    (n : SimplexCategory) (g : simplex b' ⟶ Y)
    (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    (gSide : ∀ e, simplex (b e) ⟶ Y)
    (hSide : ∀ e, SSet.stdSimplex.map (h e) ≫ g = gSide e)
    (sqSide : ∀ e, CommSq t i p (SSet.stdSimplex.map (c e) ≫ gSide e))
    (E : JTFiniteCoefficientBridgeExtension.Extension c u sq n)
    (e : Fin (m + 1)) : JTCommonCoefficientLiftChoices.Extension (sqSide e) n where
  map := SSet.stdSimplex.map (side c u h hu n e) ≫ E.map
  stationary := by
    rw [← Category.assoc (JTCommonCoefficientParameter.prism (c e) n)]
    rw [← prism_side c u n h hu e]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc, E.stationary, whiskerLeft_fst_assoc]
  over := by
    rw [Category.assoc, E.over, ← Category.assoc, ← SSet.stdSimplex.map_comp,
      side_base c u h hu n e, SSet.stdSimplex.map_comp, Category.assoc, hSide e]

/-- The original time map of a side is the time restriction of the bridge map. -/
theorem toSide_underlying_timeMap (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (h : ∀ e, b e ⟶ b') (hu : ∀ e, c e ≫ h e = u)
    (n : SimplexCategory) (g : simplex b' ⟶ Y)
    (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
    (gSide : ∀ e, simplex (b e) ⟶ Y)
    (hSide : ∀ e, SSet.stdSimplex.map (h e) ≫ g = gSide e)
    (sqSide : ∀ e, CommSq t i p (SSet.stdSimplex.map (c e) ≫ gSide e))
    (E : JTFiniteCoefficientBridgeExtension.Extension c u sq n)
    (e : Fin (m + 1)) :
    timeMap (sqSide e) n
        (JTCommonCoefficientLiftChoices.underlying (sqSide e)
          (toSide c u h hu n g sq gSide hSide sqSide E e)) =
      (simplex k ◁ SSet.stdSimplex.map (timeSide n e)) ≫
        timeMap sq (time m n) (JTFiniteCoefficientBridgeExtension.underlying c u sq E) := by
  rw [JTCommonCoefficientLiftChoices.underlying_timeMap,
    JTFiniteCoefficientBridgeExtension.underlying_timeMap]
  change JTCommonCoefficientParameter.prism (c e) n ≫
      SSet.stdSimplex.map (side c u h hu n e) ≫ E.map =
    (simplex k ◁ SSet.stdSimplex.map (timeSide n e)) ≫ prism c u n ≫ E.map
  rw [← Category.assoc, ← prism_side c u n h hu e, Category.assoc]

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeSideExtension
