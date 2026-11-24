import OrdinaryCSSInnerHorn
import OrdinaryDiscreteMapping
import RestrictionHomLiftingTranspose
import DaggerModelsPartII.InjectiveLocalEquivalences
import NativeInnerHornFactorization

/-!
# Inner fibrations for vertical restrictions of an ordinary CSS object

A horizontal inner horn induces a Kan trivial fibration of strict mapping
spaces. Transposing its lifting against a monomorphism in the vertical
variable gives the literal inner lifting property of the corresponding
vertical limit restriction. No horizontal Joyal-model identification is
assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCSSHorizontalRestrictions

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The literal horizontal inner-horn restriction is a Kan trivial
fibration for every CSS-fibrant ordinary simplicial space. -/
theorem innerHorn_mapping_trivialFibration (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W)
    (n : ℕ) (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    trivialFibrations SSet.{0}
      (DaggerNativeBisimplicialHorizontalMapping.horizontalPre
        (SSet.horn (n + 2) i).ι W) := by
  let j := (SSet.horn (n + 2) i).ι
  let d := OrdinaryCSSLocalization.discrete.map j
  have hd := OrdinaryCSSInnerHorn.innerHorn_trivialCofibration n i h0 hn
  have hc : cofibrations Space d := by
    change (InjectiveKanDiagram.modelCategory
      SimplexCategoryᵒᵖ).categoryWithCofibrations.cofibrations d
    rw [← OrdinaryCSSLocalization.exactClasses.1]
    exact hd.1
  have hw : Localization.localEquivalences
      OrdinaryCSSLocalization.localizingFamily d := by
    rw [← OrdinaryCSSLocalization.exactClasses.2]
    exact hd.2
  have hlocal := (OrdinaryCSSLocalization.isFibrant_iff W).mp hW
  have ht : trivialFibrations SSet.{0} (diagramMappingPrecomp d W) :=
    InjectiveKanDiagram.localTrivialCofibration_mapping_trivialFibration
      SimplexCategoryᵒᵖ OrdinaryCSSLocalization.localizingFamily d ⟨hc, hw⟩ W hlocal
  let e : Arrow.mk (diagramMappingPrecomp d W) ≅
      Arrow.mk (DaggerNativeBisimplicialHorizontalMapping.horizontalPre j W) :=
    Arrow.isoMk (OrdinaryDiscreteMapping.mappingIso (Δ[n + 2] : SSet.{0}) W)
      (OrdinaryDiscreteMapping.mappingIso (SSet.horn (n + 2) i).toSSet W)
      (OrdinaryDiscreteMapping.mappingIso_natural j W).symm
  exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff e).mp ht

/-- Any monomorphism in the original vertical simplicial-set variable
induces an inner fibration on the actual horizontal limit restrictions. -/
theorem restriction_innerFibration (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] :
    DaggerNativeInnerHornFactorization.innerFibrations
      (diagramRestrictionPre v W.flip) := by
  rw [DaggerNativeInnerHornFactorization.innerFibrations_iff]
  intro n i h0 hn
  apply RestrictionHomLiftingTranspose.lifting_of_hom v (SSet.horn (n + 2) i).ι
    W.flip
  have h := innerHorn_mapping_trivialFibration W hW n i h0 hn
  rw [← cofibrations_rlp] at h
  apply h v
  rw [SSet.modelCategoryQuillen.cofibrations_eq]
  exact monomorphisms.infer_property _

#print axioms innerHorn_mapping_trivialFibration
#print axioms restriction_innerFibration

end
end DaggerModels.PartII.OrdinaryCSSHorizontalRestrictions
