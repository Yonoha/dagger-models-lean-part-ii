import OrdinaryFirstRowQuillen
import OrdinaryFirstRowCounitWeak
import OrdinaryJTLeftWeak
import OrdinaryJTDiscreteRealizationIdentity

/-!
# The actual first-row Quillen equivalence

Realization of horizontal discretization is naturally the identity, so the
actual left JT functor reflects weakness of discrete maps. For every
CSS-fibrant target, the literal first-row counit is CSS weak. Factoring an
adjunction mate through that counit proves the original Quillen-equivalence
criterion for the actual first-row adjunction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra

namespace DaggerModels.PartII.OrdinaryFirstRowQuillenEquivalence

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryFirstRowAdjunction (firstRow adjunction)
open OrdinaryJTProjectiveQuillen (joyalModel)

noncomputable section

private local instance : ModelCategory SSet.{0} := joyalModel
private local instance : CategoryWithFibrations SSet.{0} := joyalModel.categoryWithFibrations
private local instance : CategoryWithCofibrations SSet.{0} := joyalModel.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  joyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory Space := OrdinaryCSSLocalization.model
private local instance : CategoryWithFibrations Space :=
  OrdinaryCSSLocalization.model.categoryWithFibrations
private local instance : CategoryWithCofibrations Space :=
  OrdinaryCSSLocalization.model.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences Space :=
  OrdinaryCSSLocalization.model.categoryWithWeakEquivalences

/-- Horizontal discretization preserves and reflects the fixed original
Joyal weak class through the actual CSS weak class. -/
theorem discrete_weak_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    weakEquivalences Space (discrete.map f) ↔ weakEquivalences SSet.{0} f := by
  constructor
  · intro hf
    have hL := OrdinaryJTLeftWeak.left_map_weak (discrete.map f) hf
    let e := OrdinaryJTDiscreteRealizationIdentity.discreteRealizationIdentityIso
    let a : Arrow.mk (OrdinaryJTCurriedAdjunction.left.map (discrete.map f)) ≅
        Arrow.mk f := Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
    exact ((weakEquivalences SSet.{0}).arrow_mk_iso_iff a).mp hL
  · exact OrdinaryFirstRowQuillen.discrete_map_weak f

/-- The actual discrete/first-row adjunction is a Quillen equivalence for
the original ordinary Joyal model and the exact ordinary CSS localization. -/
theorem isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence SSet.{0} Space _ _ joyalModel
      OrdinaryCSSLocalization.model discrete firstRow adjunction := by
  refine {
    toIsQuillenAdjunction := OrdinaryFirstRowQuillen.isQuillenAdjunction
    weakEquivalence_homEquiv_iff := ?_ }
  intro A W hA hW f
  let g := (adjunction.homEquiv A W) f
  let c := adjunction.counit.app W
  have hfac : discrete.map g ≫ c = f :=
    (adjunction.homEquiv A W).symm_apply_apply f
  have hc : weakEquivalences Space c := OrdinaryFirstRowCounitWeak.counit_weak W hW
  change WeakEquivalence g ↔ WeakEquivalence f
  simp only [weakEquivalence_iff]
  constructor
  · intro hg
    have hd := (discrete_weak_iff g).mpr hg
    have hm := (weakEquivalences Space).comp_mem (discrete.map g) c hd hc
    exact hfac ▸ hm
  · intro hf
    have hm : weakEquivalences Space (discrete.map g ≫ c) := hfac.symm ▸ hf
    have hd := (weakEquivalences Space).of_postcomp (discrete.map g) c hc hm
    exact (discrete_weak_iff g).mp hd

#print axioms discrete_weak_iff
#print axioms isQuillenEquivalence

end
end DaggerModels.PartII.OrdinaryFirstRowQuillenEquivalence
