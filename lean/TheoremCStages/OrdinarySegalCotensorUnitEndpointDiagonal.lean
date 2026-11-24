import KanHomotopyMonomorphism
import OrdinarySegalCotensorRowSwitch
import OrdinarySegalCotensorSegal

/-!
# Weak strict diagonals on both original endpoint factors

The same actual row factorization through coherent evaluation is taken in
both endpoint factors. Mathlib's stability of Kan trivial fibrations under
binary products and its monomorphism instance supply the product
factorization. This retains the original ordered endpoint map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorUnitEndpointDiagonal

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalCoherentArrowImage
open OrdinarySegalCotensorRowSwitch

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The ordered pair of the same literal unit row restriction has weak
strict diagonal on every injectively fibrant ordinary Segal space. -/
theorem unitRowPair_diagonal_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : SimplexCategory) :
    WeakEquivalence (KanHomotopyMonomorphism.diagonal
      (prod.map
        ((pre (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W).app (op n))
        ((pre (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W).app (op n)))) := by
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
  have hp₂ : trivialFibrations SSet.{0} (prod.map p p) := by
    apply MorphismProperty.limMap
    rintro (_ | _) <;> exact hp
  have fac₂ : prod.map p p ≫ prod.map m m = prod.map f f := by
    rw [prod.map_map, fac]
  exact KanHomotopyMonomorphism.diagonal_weak_of_trivialFibration_mono
    (prod.map f f) (prod.map p p) (prod.map m m) fac₂ hp₂

#print axioms unitRowPair_diagonal_weak

end
end DaggerModels.PartII.OrdinarySegalCotensorUnitEndpointDiagonal
