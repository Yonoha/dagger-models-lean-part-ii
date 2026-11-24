import OrdinarySegalHorizontalRestrictions
import OrdinaryJTRightNerveCompleteness
import NativeWeakMonoWholeRestriction
import DaggerModelsPartII.JTSimplexUnitKan

/-!
# Reflection of coherent walking extensions through a parameter vertex

Restriction along an original groupoid-simplex vertex into a horizontal
quasicategory is a Kan trivial fibration. Its lifting property reflects a
whole walking-isomorphism extension of a specified directed edge while
keeping that same edge. This uses no weak-equivalence claim about a vertical
row and no completeness assumption.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentArrowEvaluationReflection

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev i : (Δ[1] : SSet.{0}) ⟶ E :=
  JTCylinderCEComparison.simplexUnit.app ⦋1⦌

/-- A Kan trivial fibration reflects a whole walking extension of the
specified original edge, with equality on the edge and the whole base map. -/
theorem walking_extension_lift {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : trivialFibrations SSet.{0} p)
    (u : (Δ[1] : SSet.{0}) ⟶ X) (H : E ⟶ Y)
    (h : u ≫ p = i ≫ H) :
    ∃ H' : E ⟶ X, i ≫ H' = u ∧ H' ≫ p = H := by
  haveI : Mono i := JTSimplexUnitKan.simplexUnit_mono ⦋1⦌
  haveI : Cofibration i :=
    (SSet.modelCategoryQuillen.cofibration_iff i).mpr inferInstance
  have hp' := (mem_trivialFibrations_iff p).mp hp
  letI : Fibration p := hp'.1
  letI : WeakEquivalence p := hp'.2
  let sq : CommSq u i p H := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Existence of an extension along the original free-groupoid unit is
equivalent before and after an actual Kan trivial fibration. -/
theorem walking_extension_iff {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : trivialFibrations SSet.{0} p)
    (u : (Δ[1] : SSet.{0}) ⟶ X) :
    (∃ H' : E ⟶ X, i ≫ H' = u) ↔
      (∃ H : E ⟶ Y, i ≫ H = u ≫ p) := by
  constructor
  · rintro ⟨H', hH'⟩
    exact ⟨H' ≫ p, by rw [← Category.assoc, hH']⟩
  · rintro ⟨H, hH⟩
    obtain ⟨H', hH', _⟩ := walking_extension_lift p hp u H hH.symm
    exact ⟨H', hH'⟩

/-- The actual vertex restriction in any vertical limit quasicategory
reflects coherent extension of the same horizontal edge. -/
theorem parameterVertex_reflects_walking_extension (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (K : SSet.{0}) (k : SimplexCategory) (j : Fin (k.len + 1))
    (u : (Δ[1] : SSet.{0}) ⟶
      (ihom (GroupoidSimplex.parameter.obj k)).obj (diagramRestriction K W.flip)) :
    (∃ H' : E ⟶
        (ihom (GroupoidSimplex.parameter.obj k)).obj (diagramRestriction K W.flip),
        i ≫ H' = u) ↔
      (∃ H : E ⟶
        (ihom (Δ[0] : SSet.{0})).obj (diagramRestriction K W.flip),
        i ≫ H = u ≫
          (MonoidalClosed.pre (JTParameterContraction.parameterVertex k j)).app
            (diagramRestriction K W.flip)) := by
  let Z := diagramRestriction K W.flip
  let v := JTParameterContraction.parameterVertex k j
  letI : SSet.Quasicategory Z :=
    OrdinarySegalHorizontalRestrictions.restriction_quasicategory W hSegal K
  letI : Mono v := JTParameterVertexKan.vertex_mono k j
  have hv : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences v :=
    OrdinaryJTRightNerveCompleteness.parameterVertex_categorical_weak k j
  have hp : trivialFibrations SSet.{0} ((MonoidalClosed.pre v).app Z) :=
    DaggerNativeWeakMonoWholeRestriction.restriction_Kan_trivial v hv Z
  exact walking_extension_iff ((MonoidalClosed.pre v).app Z) hp u

#print axioms walking_extension_lift
#print axioms walking_extension_iff
#print axioms parameterVertex_reflects_walking_extension

end

end DaggerModels.PartII.OrdinaryCoherentArrowEvaluationReflection
