import OrdinarySSetRelativeLatchingMono
import TopCatModelCategory.ModelCategorySSet
import DaggerModelsPartII.ReedyCoefficientChange
import DaggerModelsPartII.ReedyRelativeWfs
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Monomorphisms of ordinary simplicial spaces are Reedy cofibrations

Evaluate each actual outer relative latching arrow at every inner simplex.
Evaluation preserves its latching colimit and pushout. The resulting arrow
is the relative latching map of a monomorphism of ordinary simplicial sets,
so it is injective by `OrdinarySSetRelativeLatchingMono`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySpaceReedyMono

noncomputable section

private theorem evaluated_mono
    {W V : SimplexCategoryᵒᵖ ⥤ SSet.{0}} (f : W ⟶ V) [Mono f]
    (q : SimplexCategoryᵒᵖ) :
    Mono (Functor.whiskerRight f (SSet.evaluation.{0}.obj q)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  change Mono ((f.app m).app q)
  have hm : Mono (f.app m) :=
    (NatTrans.mono_iff_mono_app f).mp inferInstance m
  exact (NatTrans.mono_iff_mono_app (f.app m)).mp hm q

/-- Every component of the original outer relative latching arrow is
injective for a monomorphism of ordinary simplicial spaces. -/
theorem relativeLatchingMap_app_mono
    {W V : SimplexCategoryᵒᵖ ⥤ SSet.{0}} (f : W ⟶ V) [Mono f]
    (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    Mono ((relativeLatchingMap n f).app q) := by
  let E := SSet.evaluation.{0}.obj q
  letI : PreservesColimitsOfSize.{0, 0} E := by
    change PreservesColimitsOfSize.{0, 0}
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj q)
    infer_instance
  letI : Mono (Functor.whiskerRight f E) := evaluated_mono f q
  have htype : Mono
      (relativeLatchingMap n (Functor.whiskerRight f E)) :=
    OrdinarySSetRelativeLatchingMono.relativeLatchingMap_mono _ n
  have hmapped : Mono (E.map (relativeLatchingMap n f)) :=
    ((monomorphisms (Type 0)).arrow_mk_iso_iff
      (ReedyCoefficientChange.relativeLatchingArrowIso E n f)).2 htype
  exact hmapped

/-- The actual outer relative latching map of a simplicial-space
monomorphism is monic as a map of simplicial sets. -/
theorem relativeLatchingMap_mono
    {W V : SimplexCategoryᵒᵖ ⥤ SSet.{0}} (f : W ⟶ V) [Mono f]
    (n : ℕ) : Mono (relativeLatchingMap n f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  exact relativeLatchingMap_app_mono f n q

/-- Every monomorphism of ordinary simplicial spaces belongs to the
literal Kan-valued Reedy cofibration class. -/
theorem mono_reedyCofibration
    {W V : SimplexCategoryᵒᵖ ⥤ SSet.{0}} (f : W ⟶ V) [Mono f] :
    reedyLatchingProperty (cofibrations SSet.{0}) f := by
  intro n
  rw [SSet.modelCategoryQuillen.cofibrations_eq]
  letI : Mono (relativeLatchingMap n f) := relativeLatchingMap_mono f n
  exact monomorphisms.infer_property _

#print axioms relativeLatchingMap_app_mono
#print axioms relativeLatchingMap_mono
#print axioms mono_reedyCofibration

end
end DaggerModels.PartII.OrdinarySpaceReedyMono
