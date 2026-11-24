import DaggerModelsPartII.ResolutionLocalCharacterization
import DaggerModelsPartII.ResolutionComparisonCriterion
import DaggerModelsPartII.ResolutionMappingComponents

/-! Comparison of the local weak class and the original Reedy weak class. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localComparisonLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localComparisonColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localComparisonCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory

section Reedy

local instance localComparisonReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

/-- On two local objects the local weak class agrees with the original Reedy weak class. -/
theorem resolutionLocalEquivalence_iff_reedyWeak_of_local
    {W V : ResolutionDiagram.{u}} (f : W ⟶ V)
    (hW : resolutionLocalObject W) (hV : resolutionLocalObject V) :
    resolutionLocalEquivalences f ↔ reedyWeakEquivalences f := by
  letI : IsFibrant W := hW.1
  letI : IsFibrant V := hV.1
  exact ⟨fun h ↦ CosimplicialResolution.weak_of_mappingTests_self f (h W hW) (h V hV),
    reedyWeakEquivalences_le_resolutionLocalEquivalences f⟩

/-- Maps between local objects are local equivalences exactly when their zero components
are dagger Joyal weak equivalences. -/
theorem resolutionLocalEquivalence_iff_evalZero_of_local
    {W V : ResolutionDiagram.{u}} (f : W ⟶ V)
    (hW : resolutionLocalObject W) (hV : resolutionLocalObject V) :
    resolutionLocalEquivalences f ↔ weakEquivalences DaggerSSet.{u} (f.app (op ⦋0⦌)) :=
  (resolutionLocalEquivalence_iff_reedyWeak_of_local f hW hV).trans
    (reedyWeakEquivalence_iff_evalZero_of_homotopicallyConstant f
      ((resolutionLocalObject_iff_homotopicallyConstant W).mp hW).2
      ((resolutionLocalObject_iff_homotopicallyConstant V).mp hV).2)

/-- The constant--evaluation adjunction satisfies the weak-equivalence criterion for
the exact local classes, using a Reedy fibrant replacement of the constant diagram. -/
theorem constantEvaluation_localEquivalence_iff {A : DaggerSSet.{u}}
    {W : ResolutionDiagram.{u}} (f : constantDiagram.obj A ⟶ W)
    (hW : resolutionLocalObject W) :
    resolutionLocalEquivalences f ↔
      weakEquivalences DaggerSSet.{u} (constantEvaluationAdjunction.homEquiv A W f) := by
  letI : IsFibrant W := hW.1
  let j := resolutionReedyFibrantReplacementUnit.app (constantDiagram.obj A)
  let T := resolutionReedyFibrantReplacement.obj (constantDiagram.obj A)
  have hj : trivialCofibrations ResolutionDiagram.{u} j :=
    resolutionReedyFibrantReplacementUnit_trivialCofibration (constantDiagram.obj A)
  have sq : CommSq f j (terminal.from W) (terminal.from T) :=
    ⟨terminal.hom_ext _ _⟩
  letI := hasLiftingProperty_of_wfs j (terminal.from W) hj (mem_fibrations _)
  let g := sq.lift
  have fac : j ≫ g = f := sq.fac_left
  have hT := resolutionReedyFibrantReplacement_constant_local A
  have hl : resolutionLocalEquivalences f ↔ resolutionLocalEquivalences g := by
    have hj' := reedyWeakEquivalences_le_resolutionLocalEquivalences j hj.2
    rw [← fac]
    exact ⟨fun h ↦ resolutionLocalEquivalences.of_precomp _ _ hj' h,
      fun h ↦ resolutionLocalEquivalences.comp_mem _ _ hj' h⟩
  have hw : reedyWeakEquivalences f ↔ reedyWeakEquivalences g := by
    change weakEquivalences ResolutionDiagram.{u} f ↔ weakEquivalences ResolutionDiagram.{u} g
    rw [← fac]
    exact ⟨fun h ↦ (weakEquivalences ResolutionDiagram.{u}).of_precomp _ _ hj.2 h,
      fun h ↦ (weakEquivalences ResolutionDiagram.{u}).comp_mem _ _ hj.2 h⟩
  exact hl.trans ((resolutionLocalEquivalence_iff_reedyWeak_of_local g hT hW).trans
    (hw.symm.trans (constantEvaluation_reedyWeak_iff f
      ((resolutionLocalObject_iff_homotopicallyConstant W).mp hW).2)))

/-- A functorial replacement by local objects computes the exact local weak class
whenever its unit consists of local equivalences. -/
theorem resolutionLocalEquivalences_iff_of_localReplacement
    (L : ResolutionDiagram.{u} ⥤ ResolutionDiagram.{u}) (η : 𝟭 _ ⟶ L)
    (hobj : ∀ W, resolutionLocalObject (L.obj W))
    (hη : ∀ W, resolutionLocalEquivalences (η.app W))
    {W V : ResolutionDiagram.{u}} (f : W ⟶ V) :
    resolutionLocalEquivalences f ↔ reedyWeakEquivalences (L.map f) := by
  have hc : f ≫ η.app V = η.app W ≫ L.map f := η.naturality f
  refine Iff.trans ?_ (resolutionLocalEquivalence_iff_reedyWeak_of_local _ (hobj W) (hobj V))
  constructor
  · intro h
    apply resolutionLocalEquivalences.of_precomp _ _ (hη W)
    rw [← hc]
    exact resolutionLocalEquivalences.comp_mem _ _ h (hη V)
  · intro h
    apply resolutionLocalEquivalences.of_postcomp _ _ (hη V)
    rw [hc]
    exact resolutionLocalEquivalences.comp_mem _ _ (hη W) h

private theorem constantDiagram_map_reedyCofibration {A B : DaggerSSet.{u}} (f : A ⟶ B)
    (hf : cofibrations DaggerSSet.{u} f) : reedyCofibrations (constantDiagram.map f) :=
  (constantDiagram.{u}.preservesCofibrations_iff.mp
    constantEvaluationAdjunction_isQuillen.toPreservesCofibrations) f hf

end Reedy

section Localized

variable [ModelCategory ResolutionDiagram.{u}]

/-- The constant--evaluation adjunction is a Quillen equivalence for any model
structure with the prescribed cofibrations, local equivalences, and local fibrant objects. -/
theorem constantEvaluation_isQuillenEquivalence_of_localizedModel
    (hc : cofibrations ResolutionDiagram.{u} = reedyCofibrations)
    (hw : weakEquivalences ResolutionDiagram.{u} = resolutionLocalEquivalences)
    (hf : ∀ W : ResolutionDiagram.{u}, IsFibrant W → resolutionLocalObject W) :
    constantEvaluationAdjunction.{u}.IsQuillenEquivalence := by
  letI hcof : constantDiagram.{u}.PreservesCofibrations := by
    apply (constantDiagram.{u}.preservesCofibrations_iff).mpr
    intro A B f h
    change cofibrations ResolutionDiagram.{u} (constantDiagram.map f)
    rw [hc]
    exact constantDiagram_map_reedyCofibration f h
  have ht : constantDiagram.{u}.PreservesTrivialCofibrations := by
    constructor
    intro A B f h
    change trivialCofibrations ResolutionDiagram.{u} (constantDiagram.map f)
    refine ⟨((constantDiagram.{u}.preservesCofibrations_iff).mp hcof) _ h.1, ?_⟩
    change weakEquivalences ResolutionDiagram.{u} (constantDiagram.map f)
    rw [hw]
    exact reedyWeakEquivalences_le_resolutionLocalEquivalences _ (fun _ ↦ h.2)
  letI := constantEvaluationAdjunction.preservesTrivialCofibrations_iff_preservesFibrations.mp ht
  exact
    { toIsQuillenAdjunction := ⟨⟩
      weakEquivalence_homEquiv_iff := by
        intro A W _ hW f
        rw [weakEquivalence_iff, weakEquivalence_iff, hw]
        exact (constantEvaluation_localEquivalence_iff f (hf W hW)).symm }

end Localized


end

end DaggerModels.PartII
