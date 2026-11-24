import DaggerModelsPartII.ResolutionLocalizedModel
import DaggerModelsPartII.LocalPushout

/-! Left properness of the prescribed local weak class from cobase-change stability. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localizationProperLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localizationProperColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localizationProperCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory

section Reedy

local instance localizationProperReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

/-- Local equivalences are stable under pushout along Reedy cofibrations. -/
theorem resolutionLocal_leftProper
    {X Y X' Y' : ResolutionDiagram.{u}} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'} (sq : IsPushout f i j f')
    (hf : resolutionLocalEquivalences f) (hi : reedyCofibrations i) :
    resolutionLocalEquivalences f' := by
  let d := factorizationData (cofibrations ResolutionDiagram.{u})
    (trivialFibrations ResolutionDiagram.{u}) f
  have hp : resolutionLocalEquivalences d.p :=
    reedyWeakEquivalences_le_resolutionLocalEquivalences d.p d.hp.2
  have hd : (reedyCofibrations ⊓ resolutionLocalEquivalences) d.i :=
    ⟨d.hi, resolutionLocalEquivalences.of_postcomp _ _ hp (d.fac.symm ▸ hf)⟩
  let sq₁ := IsPushout.of_hasPushout d.i i
  have hc : d.i ≫ d.p ≫ j = i ≫ f' := by
    rw [← Category.assoc, d.fac]
    exact sq.w
  let g := pushout.desc (d.p ≫ j) f' hc
  have hfac : pushout.inr d.i i ≫ g = f' := pushout.inr_desc _ _ _
  have comm : d.p ≫ j = pushout.inl d.i i ≫ g := (pushout.inl_desc _ _ _).symm
  have sq₂ : IsPushout d.p (pushout.inl d.i i) j g :=
    (sq₁.paste_horiz_iff comm).mp (by rw [d.fac, hfac]; exact sq)
  have h₁ := (reedyCofibrations ⊓ resolutionLocalEquivalences).of_isPushout sq₁.flip hd
  have hcof : reedyCofibrations (pushout.inl d.i i) :=
    (cofibrations ResolutionDiagram.{u}).of_isPushout sq₁ hi
  have h₂ := resolutionReedy_leftProper sq₂ d.hp.2 hcof
  rw [← hfac]
  exact resolutionLocalEquivalences.comp_mem _ _ h₁.2
    (reedyWeakEquivalences_le_resolutionLocalEquivalences g h₂)

end Reedy

/-- A model structure with the prescribed cofibrations and local weak equivalences
is automatically left proper. -/
theorem resolutionLocalizedModel_leftProper [ModelCategory ResolutionDiagram.{u}]
    (hc : cofibrations ResolutionDiagram.{u} = reedyCofibrations)
    (hw : weakEquivalences ResolutionDiagram.{u} = resolutionLocalEquivalences)
    {X Y X' Y' : ResolutionDiagram.{u}} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'} (sq : IsPushout f i j f')
    (hf : weakEquivalences ResolutionDiagram.{u} f) (hi : cofibrations ResolutionDiagram.{u} i) :
    weakEquivalences ResolutionDiagram.{u} f' := by
  exact hw.symm ▸ resolutionLocal_leftProper sq (hw ▸ hf) (hc ▸ hi)

end

end DaggerModels.PartII
