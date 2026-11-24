import DaggerModelsPartII.ResolutionLocalComparison
import DaggerModelsPartII.MappingChangeModel

/-! The fibrancy and Quillen comparison forced by the two classes of Theorem A. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localizedModelLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localizedModelColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localizedModelCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory

variable [M : ModelCategory ResolutionDiagram.{u}]
  (hc : cofibrations ResolutionDiagram.{u} = reedyCofibrations)
  (hw : weakEquivalences ResolutionDiagram.{u} = resolutionLocalEquivalences)

include hc hw in
private theorem localizedModel_fibration_le_reedy :
    fibrations ResolutionDiagram.{u} ≤ reedyFibrations := by
  have hR : (reedyCofibrations ⊓ reedyWeakEquivalences).rlp = reedyFibrations := by
    letI := resolutionReedyModelCategory.{u}
    exact rlp_eq_of_wfs (trivialCofibrations ResolutionDiagram.{u}) (fibrations ResolutionDiagram.{u})
  have hM : (reedyCofibrations ⊓ resolutionLocalEquivalences).rlp =
      fibrations ResolutionDiagram.{u} := by
    rw [← hc, ← hw]
    exact rlp_eq_of_wfs (trivialCofibrations ResolutionDiagram.{u}) (fibrations ResolutionDiagram.{u})
  rw [← hR, ← hM]
  exact antitone_rlp (inf_le_inf_left _ reedyWeakEquivalences_le_resolutionLocalEquivalences)

include hc hw in
/-- A fibrant object for the prescribed local classes passes the exact local tests in
the original Reedy model. -/
theorem resolutionLocalObject_of_localizedModel_fibrant (W : ResolutionDiagram.{u})
    (hW : IsFibrant W) : resolutionLocalObject W := by
  have hWF : fibrations ResolutionDiagram.{u} (terminal.from W) := by
    letI := hW
    exact mem_fibrations _
  have hWR := localizedModel_fibration_le_reedy hc hw _ hWF
  have hR : @IsFibrant ResolutionDiagram.{u} _ resolutionReedyModelCategory.{u}.categoryWithFibrations _ W := by
    letI := resolutionReedyModelCategory.{u}
    exact (isFibrant_iff _).mpr ((fibration_iff _).mpr hWR)
  refine ⟨hR, ?_⟩
  intro A B s hs
  have hcof : resolutionReedyModelCategory.{u}.categoryWithCofibrations.cofibrations = M.categoryWithCofibrations.cofibrations :=
    hc.symm
  apply (homotopyMappingWeakEquivalences_iff_of_cofibrations_eq resolutionReedyModelCategory M hcof W hR hW s).mpr
  apply weakEquivalences_le_homotopyMappingWeakEquivalences W s
  rw [hw]
  exact resolutionGenerators_le_localEquivalences s hs

include hc hw in
/-- Any model structure with the original Reedy cofibrations and the exact local weak
equivalences has precisely the prescribed local fibrant objects. -/
theorem localizedModel_isFibrant_iff_resolutionLocalObject (W : ResolutionDiagram.{u}) :
    IsFibrant W ↔ resolutionLocalObject W := by
  refine ⟨resolutionLocalObject_of_localizedModel_fibrant hc hw W, ?_⟩
  intro hW
  let d := factorizationData (trivialCofibrations ResolutionDiagram.{u})
    (fibrations ResolutionDiagram.{u}) (terminal.from W)
  have hY : IsFibrant d.Z :=
    (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr ((fibration_iff _).mpr d.hp)
  have hY' := resolutionLocalObject_of_localizedModel_fibrant hc hw d.Z hY
  have hd : resolutionLocalEquivalences d.i := hw ▸ d.hi.2
  have hweak := (resolutionLocalEquivalence_iff_reedyWeak_of_local d.i hW hY').mp hd
  have hcof : reedyCofibrations d.i := hc ▸ d.hi.1
  have hex : ∃ r : d.Z ⟶ W, d.i ≫ r = 𝟙 W := by
    letI := resolutionReedyModelCategory.{u}
    letI : IsFibrant W := hW.1
    have sq : CommSq (𝟙 W) d.i (terminal.from W) (terminal.from d.Z) :=
      ⟨terminal.hom_ext _ _⟩
    letI := hasLiftingProperty_of_wfs d.i (terminal.from W)
      (show trivialCofibrations ResolutionDiagram.{u} d.i from ⟨hcof, hweak⟩) (mem_fibrations _)
    exact ⟨sq.lift, sq.fac_left⟩
  obtain ⟨r, hr⟩ := hex
  let e : RetractArrow (terminal.from W) (terminal.from d.Z) :=
    { i := Arrow.homMk d.i (𝟙 _) (terminal.hom_ext _ _)
      r := Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _)
      retract := by ext <;> simp [hr] }
  exact (isFibrant_iff _).mpr ((fibration_iff _).mpr
    ((fibrations ResolutionDiagram.{u}).of_retract e
      ((fibration_iff _).mp ((isFibrant_iff _).mp hY))))

include hc hw in
/-- Fibrancy for the prescribed local model is original Reedy fibrancy and
homotopical constancy, expressed by the levelwise counit. -/
theorem localizedModel_isFibrant_iff_homotopicallyConstant (W : ResolutionDiagram.{u}) :
    IsFibrant W ↔
      @IsFibrant ResolutionDiagram.{u} _ resolutionReedyModelCategory.categoryWithFibrations _ W ∧
        reedyWeakEquivalences (resolutionCounit W) :=
  (localizedModel_isFibrant_iff_resolutionLocalObject hc hw W).trans
    (resolutionLocalObject_iff_homotopicallyConstant W)

include hc hw in
/-- The constant--evaluation Quillen equivalence follows from the two exact classes
of the localized model, with fibrancy deduced from those classes. -/
theorem constantEvaluation_isQuillenEquivalence_of_exactClasses :
    constantEvaluationAdjunction.{u}.IsQuillenEquivalence :=
  constantEvaluation_isQuillenEquivalence_of_localizedModel hc hw
    (resolutionLocalObject_of_localizedModel_fibrant hc hw)

end

end DaggerModels.PartII
