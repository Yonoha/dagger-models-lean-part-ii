import DaggerModelsPartII.JTPrismRectangle

/-!
# A horizontal rectangle coordinate obstruction

The row-major rectangle restarts time at each horizontal vertex. A horizontal
degeneracy therefore cannot act by mapping each coordinate pair separately.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTPrismRectangleHorizontal

open JTPrismRectangle

private abbrev D := code ⦋1⦌ ⦋1⦌
private abbrev E := code ⦋0⦌ ⦋1⦌
private abbrev collapse : ⦋1⦌ ⟶ ⦋0⦌ := SimplexCategory.isTerminalZero.from ⦋1⦌

private def beforeRestart : Fin (D.len + 1) := ⟨1, by decide⟩
private def afterRestart : Fin (D.len + 1) := ⟨2, by decide⟩
private def lastTime : Fin (E.len + 1) := ⟨1, by decide⟩
private def firstTime : Fin (E.len + 1) := ⟨0, by decide⟩

/-- The coordinatewise action of the horizontal collapse reverses two
consecutive rectangle indices, so it is not a simplex operator. -/
theorem no_coordinatewise_horizontal_collapse :
    ¬ ∃ f : D ⟶ E, ∀ i : Fin (D.len + 1),
      pairs ⦋0⦌ ⦋1⦌ (f.toOrderHom i) =
        (collapse.toOrderHom (pairs ⦋1⦌ ⦋1⦌ i).1,
          (pairs ⦋1⦌ ⦋1⦌ i).2) := by
  rintro ⟨f, hf⟩
  have hbefore : f.toOrderHom beforeRestart = lastTime := by
    apply (pairs ⦋0⦌ ⦋1⦌).injective
    rw [hf beforeRestart]
    decide
  have hafter : f.toOrderHom afterRestart = firstTime := by
    apply (pairs ⦋0⦌ ⦋1⦌).injective
    rw [hf afterRestart]
    decide
  have hmono : f.toOrderHom beforeRestart ≤ f.toOrderHom afterRestart :=
    f.toOrderHom.monotone (by decide)
  rw [hbefore, hafter] at hmono
  exact (by decide : ¬ lastTime ≤ firstTime) hmono

end DaggerModels.PartII.JTPrismRectangleHorizontal
