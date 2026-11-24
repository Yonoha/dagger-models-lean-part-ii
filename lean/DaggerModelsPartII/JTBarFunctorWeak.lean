import DaggerModelsPartII.JTBarDensityWeak
import ActualDaggerQuillenEquivalenceReduction

/-!
# Weak preservation by the actual bar frame realization

Naturality of the original weak beta transports the original Part I
rigidification's weak preservation to the actual bar frame realization.
This concerns the literal functor on maps, without a derived-functor API.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra DaggerModels

namespace DaggerModels.PartII.JTBarFunctorWeak

open OrdinaryRigidification.DaggerRigidification
open JTProjectiveBar JTFrameAdjunction JTBarComparison

noncomputable section

private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The actual composite of bar and frame realization sends every original
 dagger Joyal weak equivalence to an original dagger Bergner weak equivalence. -/
theorem frameRealization_bar_map_weak {X Y : DaggerSSet.{0}} (f : X ⟶ Y)
    (hf : weakEquivalences DaggerSSet.{0} f) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (frameRealization.map (barOnDagger.map f)) := by
  let P := weakEquivalences DaggerSimplicialCat.{0, 0}
  have hX : P (beta.app X) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0} _
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact JTBarDensityWeak.beta_daggerDK X
  have hY : P (beta.app Y) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0} _
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact JTBarDensityWeak.beta_daggerDK Y
  have hf' : WeakEquivalence f := (weakEquivalence_iff f).2 hf
  have hC : P (daggerRigidification.map f) :=
    (weakEquivalence_iff _).1
      ((DaggerActualQuillenEquivalenceReduction.weakEquivalence_map_iff f).2 hf')
  apply P.of_postcomp _ (beta.app Y) hY
  change P ((barOnDagger ⋙ frameRealization).map f ≫ beta.app Y)
  rw [beta.naturality f]
  exact P.comp_mem _ _ hX hC

end

end DaggerModels.PartII.JTBarFunctorWeak
