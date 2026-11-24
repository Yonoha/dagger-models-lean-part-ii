import DaggerModelsPartII.CosimplicialMappingInvariance
import DaggerModelsPartII.ReedyFibrantDiagrams

/-!
# Target weak invariance for an actual Reedy cofibrant cosimplicial diagram

The ordinary strict Hom simplicial set of a Reedy cofibrant cosimplicial
diagram sends weak maps between fibrant targets to Kan weak maps. The
diagram need not carry an augmentation or be a chosen resolution.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII.StrictFrameMappingTargetWeak

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

/-- The literal ordinary Hom simplicial set of an opposite cosimplicial diagram,
covariant in its target. -/
def mapping (D : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) : C ⥤ SSet.{v} :=
  opOp C ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj D

/-- Boundary lifting against the matching maps makes the strict target map
a Kan trivial fibration whenever the target map is an original trivial fibration. -/
theorem mapping_map_trivialFibration (D : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ)
    [IsFibrant D] {Y Z : C} (p : Y ⟶ Z) (hp : trivialFibrations C p) :
    trivialFibrations SSet.{v} ((mapping D).map p) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  intro A B i hi
  obtain ⟨n⟩ := hi
  change HasLiftingProperty (SSet.boundary n).ι (diagramHomPrecomp p.op D)
  apply diagramHomPrecomp_boundary_lifting
  have hpo : trivialCofibrations Cᵒᵖ p.op := by
    rw [trivialCofibrations_op]
    exact hp
  exact hasLiftingProperty_of_wfs p.op _ hpo
    ((reedyFibrant_iff_matchingComparison D).mp inferInstance n)

/-- Brown's factorization argument gives Kan weak invariance for the exact
strict Hom functor of any Reedy cofibrant source diagram. -/
theorem mapping_map_weak (D : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ)
    [IsFibrant D] {Y Z : C} [IsFibrant Y] [IsFibrant Z]
    (p : Y ⟶ Z) (hp : weakEquivalences C p) :
    weakEquivalences SSet.{v} ((mapping D).map p) :=
  map_weak_of_trivialFibration (mapping D)
    (fun q hq ↦ (mapping_map_trivialFibration D q hq).2) p hp

end

end DaggerModels.PartII.StrictFrameMappingTargetWeak
