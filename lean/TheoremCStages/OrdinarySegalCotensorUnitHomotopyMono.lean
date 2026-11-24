import KanHomotopyMonomorphism
import OrdinarySegalCotensorRowSwitch
import OrdinarySegalCotensorSegal

/-!
# Weak diagonals for the original cotensor unit restriction

At each literal horizontal row, the checked parameter switch identifies the
original unit restriction with coherent walking evaluation on the cotensor
by that same standard simplex. Its trivial-fibration/mono factorization
therefore proves a weak strict diagonal. This is a row theorem; transfer to
ordered endpoint fibers remains a separate obligation.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorUnitHomotopyMono

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalCoherentArrowImage
open OrdinarySegalCotensorRowSwitch

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The literal unit restriction, with unchanged parameter and row, has
weak strict diagonal on every injectively fibrant ordinary Segal space. -/
theorem unitRow_diagonal_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : SimplexCategory) :
    WeakEquivalence (KanHomotopyMonomorphism.diagonal
      ((pre (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W).app (op n))) := by
  let V := cotensor (SSet.stdSimplex.obj n) W
  have : IsFibrant V :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  have hV := OrdinarySegalCotensorSegal.cotensor_segalCondition
    (SSet.stdSimplex.obj n) W hSegal
  let f := (pre (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W).app (op n)
  let a := rowSwitchIso (GroupoidSimplex.parameter.obj ⦋1⦌) W n
  let b := rowSwitchIso (Δ[1] : SSet.{0}) W n ≪≫
    OrdinarySegalWalkingEvaluation.simplexMappingIso V 1
  let p := a.hom ≫ coherentEvaluation V
  let m := (coherentArrowSubcomplex V).ι ≫ b.inv
  have hw : a.hom ≫ OrdinarySegalWalkingEvaluation.edgeEvaluation V = f ≫ b.hom :=
    (unitRowArrowIso W n).hom.w
  have fac : p ≫ m = f := by
    dsimp only [p, m]
    rw [Category.assoc, ← Category.assoc (coherentEvaluation V),
      coherentEvaluation_inclusion, ← Category.assoc, hw, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have ht := (mem_trivialFibrations_iff _).mp
    (OrdinarySegalCoherentEvaluationTrivialFibration.coherentEvaluation_trivialFibration
      V hV)
  have : Fibration (coherentEvaluation V) := ht.1
  have : WeakEquivalence (coherentEvaluation V) := ht.2
  have hp : trivialFibrations SSet.{0} p :=
    (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩
  exact KanHomotopyMonomorphism.diagonal_weak_of_trivialFibration_mono f p m fac hp

#print axioms unitRow_diagonal_weak

end
end DaggerModels.PartII.OrdinarySegalCotensorUnitHomotopyMono
