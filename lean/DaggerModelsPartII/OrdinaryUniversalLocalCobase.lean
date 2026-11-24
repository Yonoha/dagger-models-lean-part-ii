import DaggerModelsPartII.OrdinaryGeneratorCobase
import OriginalOrdinaryHomRetractsReconciled
import OriginalICellUniversalRecovered
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Universal ordinary local cobase comparison

The exact original ordinary generating family has a property that survives
every supplied cobase change: Hom monicity and preservation of the geometric
local comparison under a further supplied cobase change. This module packages
that property as a morphism class. Transfinite closure is proved separately.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra DaggerModels

universe u

namespace DaggerModels.OrdinaryUniversalLocalCobase

noncomputable section

/-- The original ordinary local geometric condition on every ordered Hom. -/
abbrev LocalGeometric {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : Prop :=
  ∀ x y : C.Obj, DaggerOrdinaryCellComparisonGeometric.GW (F.map x y)

/-- The original ordinary local Hom monomorphism class. -/
abbrev localHomMono : MorphismProperty SimplicialCat.{u, u} :=
  OriginalOrdinaryHomRetracts.localHomProperty
    (MorphismProperty.monomorphisms SSet.{u})

/-- Every supplied cobase of a local geometric comparison along this arrow
remains locally geometric. -/
def BaseLocal : MorphismProperty SimplicialCat.{u, u} :=
  fun C PC i ↦
    ∀ {D PD : SimplicialCat.{u, u}}
      (F : C ⟶ D) (j : D ⟶ PD) (Fplus : PC ⟶ PD),
      IsPushout F i j Fplus → LocalGeometric F → LocalGeometric Fplus

/-- Universal ordinary local comparison together with universal Hom monicity. -/
def U : MorphismProperty SimplicialCat.{u, u} :=
  DaggerICellLocalComparison.UniversalCobase (localHomMono ⊓ BaseLocal)

instance U_cobase_stable : U.IsStableUnderCobaseChange :=
  DaggerICellLocalComparison.universalCobase_stable _

instance U_respectsIso : U.RespectsIso :=
  DaggerICellLocalComparison.universalCobase_respectsIso _

/-- The identity cobase recovers Hom monicity of the original arrow. -/
theorem U_le_localHomMono : U ≤ localHomMono := by
  intro C PC i hi
  have h : (localHomMono ⊓ BaseLocal) i :=
    DaggerICellLocalComparison.universalCobase_le _ i hi
  exact h.1

/-- The identity cobase recovers local comparison preservation. -/
theorem U_le_BaseLocal : U ≤ BaseLocal := by
  intro C PC i hi
  have h : (localHomMono ⊓ BaseLocal) i :=
    DaggerICellLocalComparison.universalCobase_le _ i hi
  intro D PD F j Fplus sq hF
  exact h.2 F j Fplus sq hF

/-- Every original ordinary generator satisfies the universal property,
because its arbitrary actual pushouts have both required properties. -/
theorem generators_le_U : OrdinaryBergnerGenerators.generators.{u} ≤ U := by
  intro A B g hg
  apply (DaggerICellLocalComparison.universalCobase_iff _ g).2
  intro C PC a b i sq
  exact OrdinaryGeneratorCobase.generator_pushout_properties
    g hg a b i sq.flip

end

end DaggerModels.OrdinaryUniversalLocalCobase
