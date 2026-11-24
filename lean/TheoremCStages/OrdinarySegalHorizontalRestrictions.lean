import OrdinarySegalInnerHorn
import OrdinaryDiscreteMapping
import RestrictionHomLiftingTranspose
import DaggerModelsPartII.InjectiveLocalEquivalences
import OrdinaryCSSRestrictionQuasicategory

/-!
# Relative horizontal quasicategories for noncomplete ordinary Segal spaces

The spine-only Segal localization makes horizontal inner-horn restrictions
Kan trivial fibrations. Transposition against an arbitrary vertical monomorphism
gives an inner fibration of horizontal limit restrictions. Restricting from the
empty vertical parameter proves these are quasicategories. Ordinary completeness
is never assumed. The empty-restriction terminal lemma is reused in its actual
unconditional scope, despite its older CSS-prefixed module name.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalHorizontalRestrictions

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- All actual horizontal inner-horn restrictions are Kan trivial fibrations
for any ordinary Kan-injective Segal space, without ordinary completeness. -/
theorem innerHorn_mapping_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (n : ℕ) (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    trivialFibrations SSet.{0}
      (DaggerNativeBisimplicialHorizontalMapping.horizontalPre
        (SSet.horn (n + 2) i).ι W) := by
  let j := (SSet.horn (n + 2) i).ι
  let d := OrdinaryCSSLocalization.discrete.map j
  have hd := OrdinarySegalInnerHorn.innerHorn_trivialCofibration n i h0 hn
  have hc : cofibrations Space d := by
    change (InjectiveKanDiagram.modelCategory
      SimplexCategoryᵒᵖ).categoryWithCofibrations.cofibrations d
    rw [← OrdinarySegalLocalization.exactClasses.1]
    exact hd.1
  have hw : Localization.localEquivalences
      OrdinarySegalLocalization.localizingFamily d := by
    rw [← OrdinarySegalLocalization.exactClasses.2]
    exact hd.2
  have hlocal : Localization.localObject OrdinarySegalLocalization.localizingFamily W :=
    (OrdinarySegalLocalization.localObject_iff_strict W).mpr ⟨inferInstance, hSegal⟩
  have ht : trivialFibrations SSet.{0} (diagramMappingPrecomp d W) :=
    InjectiveKanDiagram.localTrivialCofibration_mapping_trivialFibration
      SimplexCategoryᵒᵖ OrdinarySegalLocalization.localizingFamily d ⟨hc, hw⟩ W hlocal
  let e : Arrow.mk (diagramMappingPrecomp d W) ≅
      Arrow.mk (DaggerNativeBisimplicialHorizontalMapping.horizontalPre j W) :=
    Arrow.isoMk (OrdinaryDiscreteMapping.mappingIso (Δ[n + 2] : SSet.{0}) W)
      (OrdinaryDiscreteMapping.mappingIso (SSet.horn (n + 2) i).toSSet W)
      (OrdinaryDiscreteMapping.mappingIso_natural j W).symm
  exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff e).mp ht

/-- Every vertical monomorphism induces an actual inner fibration on horizontal
limit restrictions of a Kan-injective ordinary Segal space. -/
theorem restriction_innerFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] :
    DaggerNativeInnerHornFactorization.innerFibrations
      (diagramRestrictionPre v W.flip) := by
  rw [DaggerNativeInnerHornFactorization.innerFibrations_iff]
  intro n i h0 hn
  apply RestrictionHomLiftingTranspose.lifting_of_hom v (SSet.horn (n + 2) i).ι W.flip
  have h := innerHorn_mapping_trivialFibration W hSegal n i h0 hn
  rw [← cofibrations_rlp] at h
  apply h v
  rw [SSet.modelCategoryQuillen.cofibrations_eq]
  exact monomorphisms.infer_property _

/-- Every vertical limit restriction is a genuine quasicategory, including
both sides of the relative vertical-boundary lifting problems. -/
theorem restriction_quasicategory (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (K : SSet.{0}) :
    SSet.Quasicategory (diagramRestriction K W.flip) := by
  let v : (⊥_ SSet.{0}) ⟶ K := initial.to K
  have : Mono v := inferInstance
  exact (DaggerNativeInnerHornFactorization.quasicategory_iff_inner_terminal
    (diagramRestrictionPre v W.flip)
    (OrdinaryCSSRestrictionQuasicategory.emptyRestriction_terminal W)).mpr
      (restriction_innerFibration W hSegal v)

#print axioms innerHorn_mapping_trivialFibration
#print axioms restriction_innerFibration
#print axioms restriction_quasicategory

end

end DaggerModels.PartII.OrdinarySegalHorizontalRestrictions
