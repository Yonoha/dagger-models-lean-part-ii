import OrdinarySegalHorizontalRestrictions
import OrdinaryDiscreteMapping
import NativeIhomQuasicategories
import NativeStandardSpineInner
import NativeBoundaryJoyalMappingWeak

/-!
# Inner-anodyne horizontal mapping tests in an ordinary Segal space

The checked vertical restriction is inner-right. An arbitrary inner-left
horizontal map therefore lifts against it. The existing restriction--Hom
transpose gives every vertical boundary lift, proving the strict mapping
restriction is a Kan trivial fibration. The actual closed adjunction also
transfers inner-left maps through horizontal tensor by any parameter.
No ordinary completeness hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory MonoidalClosed
open DaggerNativeInnerHornFactorization DaggerNativeIhomQuasicategories
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalInnerAnodyneMapping

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Tensoring an actual inner-left map with any original horizontal
parameter remains inner-left, by the same native closed adjunction. -/
theorem tensor_innerAnodyne (K : SSet.{0}) {A B : SSet.{0}} (i : A ⟶ B)
    (hi : innerAnodyne i) : innerAnodyne (K ◁ i) := by
  intro E T p hp
  apply ((ihom.adjunction K).hasLiftingProperty_iff i p).mpr
  exact hi ((ihom K).map p) (ihom_map_inner K p hp)

/-- Every original inner-left map induces a Kan trivial fibration of
native horizontal mapping objects into a noncomplete ordinary Segal space. -/
theorem horizontalPre_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    {A B : SSet.{0}} (i : A ⟶ B) (hi : innerAnodyne i) :
    trivialFibrations SSet.{0}
      (DaggerNativeBisimplicialHorizontalMapping.horizontalPre i W) := by
  apply (DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_iff_trivialFibration _).mp
  intro n
  have hp := OrdinarySegalHorizontalRestrictions.restriction_innerFibration
    W hSegal (SSet.boundary n).ι
  exact diagramHomPrecomp_lifting_of_restriction (SSet.boundary n).ι i W.flip
    (hi (diagramRestrictionPre (SSet.boundary n).ι W.flip) hp)

/-- The same result for the unchanged strict ordinary discrete-diagram
mapping space, retaining its actual precomposition map. -/
theorem mappingPrecomp_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    {A B : SSet.{0}} (i : A ⟶ B) (hi : innerAnodyne i) :
    trivialFibrations SSet.{0} (diagramMappingPrecomp (discrete.map i) W) := by
  let e : Arrow.mk (diagramMappingPrecomp (discrete.map i) W) ≅
      Arrow.mk (DaggerNativeBisimplicialHorizontalMapping.horizontalPre i W) :=
    Arrow.isoMk (OrdinaryDiscreteMapping.mappingIso B W)
      (OrdinaryDiscreteMapping.mappingIso A W)
      (OrdinaryDiscreteMapping.mappingIso_natural i W).symm
  exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff e).mpr
    (horizontalPre_trivialFibration W hSegal i hi)

/-- The actual tensor of a standard spine is a Kan trivial-fibration
mapping test, for every horizontal parameter and dimension. -/
theorem tensor_spine_mapping_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (K : SSet.{0}) (n : ℕ) :
    trivialFibrations SSet.{0}
      (diagramMappingPrecomp
        (discrete.map (K ◁ (DaggerNativeStandardSpineInner.spine n).ι)) W) :=
  mappingPrecomp_trivialFibration W hSegal _
    (tensor_innerAnodyne K _ (DaggerNativeStandardSpineInner.inclusion_innerAnodyne n))

#print axioms tensor_innerAnodyne
#print axioms horizontalPre_trivialFibration
#print axioms mappingPrecomp_trivialFibration
#print axioms tensor_spine_mapping_trivialFibration

end

end DaggerModels.PartII.OrdinarySegalInnerAnodyneMapping
