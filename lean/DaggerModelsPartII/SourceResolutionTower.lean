import DaggerModelsPartII.SourceResolutionLimit
import DaggerModelsPartII.InverseTowerLifting
import DaggerModelsPartII.ResolutionLocality

/-! Passage from successor mapping tests to the bottom-to-colimit mapping test. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u t z

namespace DaggerModels.PartII

noncomputable section

local instance sourceResolutionTowerLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance sourceResolutionTowerColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance sourceResolutionTowerCoefficientModel : ModelCategory DaggerSSet.{u} := DaggerOriginalJoyalModel.standardModelCategory
local instance sourceResolutionTowerReedyModel : ModelCategory ResolutionDiagram.{u} := resolutionReedyModelCategory

private abbrev OppositeSources := SimplexCategoryᵒᵖ ⥤ ResolutionDiagram.{u}ᵒᵖ

local instance sourceResolutionTowerOppositeModel : ModelCategory OppositeSources.{u} :=
  simplicialReedyModelCategory ResolutionDiagram.{u}ᵒᵖ

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {X : J ⥤ ResolutionDiagram.{u}}

/-- The source resolutions arranged as a continuous inverse tower, with the
augmentation over the original direct diagram. -/
structure SourceResolutionTower (X : J ⥤ ResolutionDiagram.{u}) where
  diagrams : Jᵒᵖ ⥤ OppositeSources.{u}
  augmentation : X.op ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ diagrams
  degreewise : ∀ j n, trivialFibrations ResolutionDiagram.{u}
    ((augmentation.app (op j)).app n).unop
  fibrant : ∀ j : J, IsFibrant (diagrams.obj (op j))
  continuous : diagrams.rightOp.IsWellOrderContinuous
  successor : ∀ (j : J), ¬IsMax j →
    fibrations OppositeSources.{u} (diagrams.map (homOfLE (Order.le_succ j)).op)

namespace SourceResolutionTower

variable (T : SourceResolutionTower X)

/-- The pointwise source resolution at an index of the tower. -/
def atIndex (j : J) : PointwiseSourceResolution (X.obj j) :=
  ⟨T.diagrams.obj (op j), T.augmentation.app (op j), T.degreewise j, T.fibrant j⟩

private theorem preservesLimits_mapping (Z : ResolutionDiagram.{u})
    {K : Type t} [Category.{z} K] [HasLimitsOfShape K ResolutionDiagram.{u}ᵒᵖ] :
    PreservesLimitsOfShape K (CosimplicialResolution.mappingFromOppositeDiagram Z) := by
  let F := coyoneda.obj (op (op Z))
  letI : PreservesLimitsOfShape K F := coyonedaPreservesLimitsOfShape _ _
  exact CategoryTheory.whiskeringRight_preservesLimitsOfShape F

include T in
/-- For a continuous tower of source resolutions, the successor mapping tests
imply the test on the map from the bottom object to the colimit. -/
theorem mapping_weak_toColimit {cX : Cocone X} (hX : IsColimit cX)
    (Z : ResolutionDiagram.{u}) [IsFibrant Z]
    (h : ∀ (j : J), ¬IsMax j →
      homotopyMappingWeakEquivalences Z (X.map (homOfLE (Order.le_succ j)))) :
    homotopyMappingWeakEquivalences Z (cX.ι.app ⊥) := by
  letI : HasColimitsOfSize.{0, u} ResolutionDiagram.{u} := hasColimitsOfSizeShrink.{0, u} _
  letI := T.continuous
  letI := T.fibrant ⊥
  let G := T.diagrams
  let cG := limit.cone G
  let hG := limit.isLimit G
  have hf : fibrations OppositeSources.{u} (cG.π.app (op ⊥)) := by
    rw [← rlp_eq_of_wfs (trivialCofibrations OppositeSources.{u}) (fibrations OppositeSources.{u})]
    apply rlp_limitProjection_of_inverseTower _ G hG
    intro j hj
    rw [rlp_eq_of_wfs (trivialCofibrations OppositeSources.{u}) (fibrations OppositeSources.{u})]
    exact T.successor j hj
  letI : Fibration (cG.π.app (op ⊥)) := (fibration_iff _).mpr hf
  have hcG : IsFibrant cG.pt := isFibrant_of_fibration (cG.π.app (op ⊥))
  let L := sourceResolutionAtLimit X G T.augmentation cX cG hG hX T.degreewise hcG
  let d : (T.atIndex ⊥).Comparison L (cX.ι.app ⊥) :=
    ⟨cG.π.app (op ⊥), sourceResolutionLimitAugmentation_fac X G T.augmentation cX cG hG ⊥⟩
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  letI : (G ⋙ F).rightOp.IsWellOrderContinuous :=
    inverseTower_continuous_map G F (fun j _ ↦ preservesLimits_mapping Z)
  letI : PreservesLimitsOfShape Jᵒᵖ F := preservesLimits_mapping Z
  have hm : SSet.modelCategoryQuillen.I.rlp (F.map d.map) := by
    change SSet.modelCategoryQuillen.I.rlp ((F.mapCone cG).π.app (op ⊥))
    apply rlp_limitProjection_of_inverseTower _ (G ⋙ F) (isLimitOfPreserves F hG)
    intro j hj
    let e : (T.atIndex j).Comparison (T.atIndex (Order.succ j))
        (X.map (homOfLE (Order.le_succ j))) :=
      ⟨G.map (homOfLE (Order.le_succ j)).op,
        T.augmentation.naturality (homOfLE (Order.le_succ j)).op |>.symm⟩
    rw [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
    exact e.mapping_trivialFibration (T.successor j hj) Z (h j hj)
  rw [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations] at hm
  exact (d.mapping_weak_iff Z).mpr hm.2

/-- The local weak-equivalence test passes to the composite of a transfinite
diagram once that diagram has been equipped with its continuous source tower. -/
theorem localEquivalence_of_transfiniteComposition {A B : ResolutionDiagram.{u}}
    {f : A ⟶ B} (c : CategoryTheory.TransfiniteCompositionOfShape J f)
    (S : SourceResolutionTower c.F)
    (h : ∀ (j : J), ¬IsMax j →
      resolutionLocalEquivalences (c.F.map (homOfLE (Order.le_succ j)))) :
    resolutionLocalEquivalences f := by
  intro Z hZ
  letI := hZ.1
  have hh := S.mapping_weak_toColimit c.isColimit Z (fun j hj ↦ h j hj Z hZ)
  rw [← c.fac]
  exact (homotopyMappingWeakEquivalences Z).comp_mem _ _
    (weakEquivalences_le_homotopyMappingWeakEquivalences Z _
      ((weakEquivalences ResolutionDiagram.{u}).of_isIso _)) hh

end SourceResolutionTower

end

end DaggerModels.PartII
