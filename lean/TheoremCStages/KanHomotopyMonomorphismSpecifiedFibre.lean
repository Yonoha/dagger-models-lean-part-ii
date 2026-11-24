import KanHomotopyMonomorphismFibreCalibration

/-!
# Weak diagonals with the original specified image point

The paired-fiber argument uses a composite point. The literal ordered
mapping fiber instead specifies its actual image point and the exact
commuting equality. Substitution retains that original API and its maps.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.KanHomotopyMonomorphismSpecifiedFibre

noncomputable section

/-- Weak strict diagonals descend to the literal fiber map at a specified
point and its specified actual image, with the original point equality. -/
theorem fibreMap_diagonal_weak {X Y A B : SSet.{0}}
    (p : X ⟶ A) (q : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : p ≫ g = f ≫ q) (b : (Δ[0] : SSet.{0}) ⟶ A)
    (d : (Δ[0] : SSet.{0}) ⟶ B) (hb : b ≫ g = d)
    [Fibration p] [Fibration q]
    (hc : Fibration (KanHomotopyMonomorphismFibre.corner p q f g h))
    [WeakEquivalence (KanHomotopyMonomorphism.diagonal f)]
    [WeakEquivalence (KanHomotopyMonomorphism.diagonal g)] :
    WeakEquivalence (KanHomotopyMonomorphism.diagonal
      (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap p q f g h b d hb)) := by
  subst d
  exact KanHomotopyMonomorphismFibreCalibration.exactFibreMap_diagonal_weak
    p q f g h b hc

#print axioms fibreMap_diagonal_weak

end
end DaggerModels.PartII.KanHomotopyMonomorphismSpecifiedFibre
