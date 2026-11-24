import OrdinaryCSSOuterFaces
import OrdinaryInnerHornFromOuterFaces

/-!
# The literal horizontal inner horns are CSS trivial cofibrations

The existing outer-face pushout proof and the finite inner-face attachment
induction apply to the inverse image of the actual CSS trivial cofibrations.
Cancellation is used only when the remaining factor is monic, as required
by the simplex inclusions in the published argument.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OrdinaryCSSInnerHorn

open OrdinaryCSSLocalization

noncomputable section

private local instance : ModelCategory Space := model

private abbrev P : MorphismProperty SSet.{0} :=
  (trivialCofibrations Space).inverseImage discrete

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
      (SimplicialObject.const (Type 0)))
  infer_instance

private instance : (trivialCofibrations Space).IsStableUnderCobaseChange := by
  rw [← fibrations_llp]
  infer_instance

private instance : P.IsStableUnderCobaseChange where
  of_isPushout sq hf :=
    (trivialCofibrations Space).of_isPushout (sq.map discrete) hf

private theorem cancel_mono {A B C : SSet.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : Mono g) (hf : P f) (hfg : P (f ≫ g)) : P g := by
  haveI := hg
  constructor
  · change model.categoryWithCofibrations.cofibrations (discrete.map g)
    rw [exactClasses.1]
    letI : ModelCategory Space :=
      InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
    change cofibrations Space (discrete.map g)
    rw [InjectiveKanDiagram.model_cofibrations]
    exact discrete_map_mono g
  · apply (weakEquivalences Space).of_precomp (discrete.map f) (discrete.map g) hf.2
    simpa only [Functor.map_comp] using hfg.2

/-- Every original horizontal inner horn, with its original dimension and
index, is a trivial cofibration in the actual ordinary CSS localization. -/
theorem innerHorn_trivialCofibration (n : ℕ) (i : Fin (n + 3))
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    @trivialCofibrations Space _ model.categoryWithCofibrations
      model.categoryWithWeakEquivalences _ _
      (discrete.map (SSet.horn (n + 2) i).ι) := by
  apply OrdinaryInnerHornFromOuterFaces.innerHorn_of_outerFaces P
    cancel_mono OrdinaryCSSOuterFaces.outerFaceMap_trivialCofibration n i
  · exact ne_of_gt h0
  · exact ne_of_lt hn

#print axioms innerHorn_trivialCofibration

end
end DaggerModels.PartII.OrdinaryCSSInnerHorn
