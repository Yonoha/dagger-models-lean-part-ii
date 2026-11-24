import DaggerModelsPartII.ChosenHomotopyFiberComparison

/-!
# The actual strict-fiber inclusion and the chosen comparison triangle

The original arrow is factored at its unchanged base. Its factorization unit
induces a canonical map from the strict fiber to the chosen homotopy fiber.
The comparison through a genuine resolved fibration restricts to the original
fiber map, as an equality of the specified maps. The original projection is
not assumed fibrant for this equality.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ChosenHomotopyFiberTriangle

open ChosenHomotopyFiberComparison
open DaggerNativeSSetFibrationSquareFibreWeak

noncomputable section

/-- The factorization unit induces the canonical strict-to-chosen-fiber map,
keeping the same base object and the same specified point. -/
def inclusion {X B K : SSet.{u}} (p : X ⟶ B) (b : K ⟶ B) :
    pullback p b ⟶ chosenFiber p b :=
  fibreMap p (replacement p).p (replacement p).i (𝟙 B)
    (by rw [Category.comp_id, (replacement p).fac]) b b (Category.comp_id b)

/-- The canonical inclusion's total projection is the actual factorization unit. -/
theorem inclusion_fst {X B K : SSet.{u}} (p : X ⟶ B) (b : K ⟶ B) :
    inclusion p b ≫ pullback.fst (replacement p).p b =
      pullback.fst p b ≫ (replacement p).i :=
  fibreMap_fst _ _ _ _ _ _ _ _

/-- The canonical inclusion retains the unchanged point-object projection. -/
theorem inclusion_snd {X B K : SSet.{u}} (p : X ⟶ B) (b : K ⟶ B) :
    inclusion p b ≫ pullback.snd (replacement p).p b = pullback.snd p b :=
  fibreMap_snd _ _ _ _ _ _ _ _

/-- The canonical strict-to-chosen-fiber map followed by the actual chosen
comparison is exactly the original specified fiber map of the square. -/
theorem inclusion_comparison {X Y B D K : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) [Fibration q]
    (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d) :
    inclusion p b ≫ comparison p q f g h b d hb =
      fibreMap p q f g h b d hb := by
  apply pullback.hom_ext
  · dsimp only [comparison]
    rw [Category.assoc, fibreMap_fst, ← Category.assoc, inclusion_fst,
      Category.assoc, replacement_i_comparisonTotal, fibreMap_fst]
  · dsimp only [comparison]
    rw [Category.assoc, fibreMap_snd, inclusion_snd, fibreMap_snd]

/-- If the original projection already is a Kan fibration, its canonical
strict-to-chosen-fiber map is weak by the retained native fiber theorem. -/
theorem inclusion_weak {X B K : SSet.{u}} (p : X ⟶ B) (b : K ⟶ B)
    [Fibration p] : WeakEquivalence (inclusion p b) := by
  haveI : Fibration (replacement p).p := (fibration_iff _).mpr (replacement p).hp
  haveI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  exact fibreMap_weakEquivalence _ _ _ _ _ _ _ _

end

end DaggerModels.PartII.ChosenHomotopyFiberTriangle
