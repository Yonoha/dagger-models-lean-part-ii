import OrdinarySegalOuterFaces
import OrdinaryInnerHornFromOuterFaces

/-!
# Inner horns are local before imposing ordinary completeness

Apply the checked finite face-union induction to the spine-only ordinary
Segal model. The cancellation step uses monicity of the remaining factor,
not the invalid unrestricted cancellation property for trivial cofibrations.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OrdinarySegalInnerHorn

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalLocalization (model)

noncomputable section

private local instance : ModelCategory Space := model

private abbrev P : MorphismProperty SSet.{0} :=
  (trivialCofibrations Space).inverseImage discrete

private instance : (trivialCofibrations Space).IsStableUnderCobaseChange := by
  rw [← fibrations_llp]
  infer_instance

private instance : P.IsStableUnderCobaseChange where
  of_isPushout sq hf :=
    (trivialCofibrations Space).of_isPushout (sq.map discrete) hf

private theorem cancel_mono {A B C : SSet.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : Mono g) (hf : P f) (hfg : P (f ≫ g)) : P g := by
  have := hg
  constructor
  · change model.categoryWithCofibrations.cofibrations (discrete.map g)
    rw [OrdinarySegalOuterFaces.cofibrations_eq_monomorphisms]
    exact OrdinaryCSSLocalization.discrete_map_mono g
  · apply (weakEquivalences Space).of_precomp (discrete.map f) (discrete.map g) hf.2
    simpa only [Functor.map_comp] using hfg.2

/-- All actual inner horns are trivial cofibrations for the spine-only model. -/
theorem innerHorn_trivialCofibration (n : ℕ) (i : Fin (n + 3))
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    @trivialCofibrations Space _ model.categoryWithCofibrations
      model.categoryWithWeakEquivalences _ _
      (discrete.map (SSet.horn (n + 2) i).ι) := by
  apply OrdinaryInnerHornFromOuterFaces.innerHorn_of_outerFaces P
    cancel_mono OrdinarySegalOuterFaces.outerFace_trivialCofibration n i
  · exact ne_of_gt h0
  · exact ne_of_lt hn

#print axioms innerHorn_trivialCofibration

end

end DaggerModels.PartII.OrdinarySegalInnerHorn
