import OrdinaryCSSConditions
import OrdinaryDiscreteMapping
import RestrictionHomLiftingTranspose
import DaggerModelsPartII.DiagramMappingPrecompFibration

/-!
# The exact walking-isomorphism lifting test on vertical restrictions

Completeness gives a Kan trivial fibration for the registered ordinary
walking-isomorphism vertex. The restriction/Hom lifting equivalence then
transfers this test through every original vertical monomorphism.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCSSWalkingRestrictions

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The actual completeness vertex induces a Kan trivial fibration on
horizontal mapping spaces into any CSS-fibrant target. -/
theorem walking_mapping_trivialFibration (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W) :
    trivialFibrations SSet.{0}
      (DaggerNativeBisimplicialHorizontalMapping.horizontalPre
        (JTParameterContraction.parameterVertex ⦋1⦌ 0) W) := by
  have hconditions := (OrdinaryCSSConditions.isFibrant_iff W).mp hW
  haveI := hconditions.1
  let d := OrdinaryCSSLocalization.completenessMap
  haveI : Mono d := OrdinaryCSSLocalization.completenessMap_mono
  have hf : Fibration (diagramMappingPrecomp d W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration SimplexCategoryᵒᵖ d W
  have ht : trivialFibrations SSet.{0} (diagramMappingPrecomp d W) :=
    ⟨(fibration_iff _).mp hf, hconditions.2.2⟩
  let j := JTParameterContraction.parameterVertex ⦋1⦌ 0
  let e : Arrow.mk (diagramMappingPrecomp d W) ≅
      Arrow.mk (DaggerNativeBisimplicialHorizontalMapping.horizontalPre j W) :=
    Arrow.isoMk
      (OrdinaryDiscreteMapping.mappingIso (GroupoidSimplex.parameter.obj ⦋1⦌) W)
      (OrdinaryDiscreteMapping.mappingIso (Δ[0] : SSet.{0}) W)
      (OrdinaryDiscreteMapping.mappingIso_natural j W).symm
  exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff e).mp ht

/-- The actual selected vertex of the original walking isomorphism lifts
against every vertical monomorphism restriction of a CSS-fibrant target. -/
theorem restriction_walking_lifting (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] :
    HasLiftingProperty (JTParameterContraction.parameterVertex ⦋1⦌ 0)
      (diagramRestrictionPre v W.flip) := by
  apply RestrictionHomLiftingTranspose.lifting_of_hom v
    (JTParameterContraction.parameterVertex ⦋1⦌ 0) W.flip
  have h := walking_mapping_trivialFibration W hW
  rw [← cofibrations_rlp] at h
  apply h v
  rw [SSet.modelCategoryQuillen.cofibrations_eq]
  exact monomorphisms.infer_property _

#print axioms walking_mapping_trivialFibration
#print axioms restriction_walking_lifting

end
end DaggerModels.PartII.OrdinaryCSSWalkingRestrictions
