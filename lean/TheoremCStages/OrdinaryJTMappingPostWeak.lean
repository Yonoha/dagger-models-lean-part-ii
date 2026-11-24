import OrdinaryJTMappingCornerComparison
import DaggerModelsPartII.StrictFrameMappingTargetWeak

/-!
# Target invariance of the literal ordinary JT mapping rows

`StrictFrameMappingTargetWeak` already proves boundary lifting and Brown
invariance for any Reedy cofibrant opposite frame. The original JT frame is
such a frame by `OrdinaryJTMappingFrameWeak.frame_op_isFibrant`.
`OrdinaryJTMappingCornerComparison.rowIso_post` transports that result to
the exact `mappingPost` used in the ordinary JT endpoint square.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTMappingPostWeak

open OrdinaryJTMappingFrameWeak OrdinaryJTMappingCornerFibration

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

/-- Postcomposition on every literal `A × J[•]` mapping row, functorially. -/
def postFunctor (A : SSet.{0}) : SSet.{0} ⥤ SSet.{0} :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (frame A).op

/-- The functor acts by the actual target map of the ordinary JT corner. -/
theorem postFunctor_map {X Y : SSet.{0}} (p : X ⟶ Y) (A : SSet.{0}) :
    (postFunctor A).map p = mappingPost p A := rfl

/-- The native diagram-Hom map and literal mapping-row map are isomorphic
as arrows, preserving both original targets and their chosen parameters. -/
def postArrowIso {X Y : SSet.{0}} (p : X ⟶ Y) (A : SSet.{0}) :
    Arrow.mk (diagramHomPrecomp p.op (frame A).op) ≅
      Arrow.mk (mappingPost p A) :=
  Arrow.isoMk (rowIso X A) (rowIso Y A)
    (OrdinaryJTMappingCornerComparison.rowIso_post p A)

private theorem joyal_fibrant (X : SSet.{0}) [X.Quasicategory] :
    @IsFibrant SSet.{0} _ ordinaryJoyalModel.categoryWithFibrations _ X := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  letI : CategoryWithFibrations SSet.{0} :=
    ordinaryJoyalModel.categoryWithFibrations
  apply (isFibrant_iff_of_isTerminal (terminal.from X)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change ordinaryJoyalModel.categoryWithFibrations.fibrations (terminal.from X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

/-- An original Joyal trivial fibration induces a Kan trivial fibration on
the literal ordinary JT mapping row for every horizontal coefficient. -/
theorem mappingPost_trivialFibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : ordinaryJoyalModel.categoryWithFibrations.fibrations p)
    (hw : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences p)
    (A : SSet.{0}) :
    trivialFibrations SSet.{0} (mappingPost p A) := by
  have hnative := by
    letI : ModelCategory SSet.{0} := ordinaryJoyalModel
    letI : CategoryWithFibrations SSet.{0} :=
      ordinaryJoyalModel.categoryWithFibrations
    letI : CategoryWithWeakEquivalences SSet.{0} :=
      ordinaryJoyalModel.categoryWithWeakEquivalences
    letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
    letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
      simplicialReedyModelCategory SSet.{0}ᵒᵖ
    letI : IsFibrant (frame A).op := frame_op_isFibrant A
    have htriv : trivialFibrations SSet.{0} p := by
      refine ⟨hp, ?_⟩
      change ordinaryJoyalModel.categoryWithWeakEquivalences.weakEquivalences p
      rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
      exact hw
    exact StrictFrameMappingTargetWeak.mapping_map_trivialFibration
      (frame A).op p htriv
  have hdiagram : trivialFibrations SSet.{0}
      (diagramHomPrecomp p.op (frame A).op) := by
    change trivialFibrations SSet.{0}
      ((StrictFrameMappingTargetWeak.mapping (frame A).op).map p)
    exact hnative
  exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff
    (postArrowIso p A)).1 hdiagram

/-- A weak categorical equivalence between original quasicategories induces
a Kan weak equivalence on every literal ordinary JT mapping row. -/
theorem mappingPost_weak {X Y : SSet.{0}} [X.Quasicategory] [Y.Quasicategory]
    (p : X ⟶ Y)
    (hp : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences p)
    (A : SSet.{0}) : DaggerSSetGluing.GW (mappingPost p A) := by
  have hnative := by
    letI : ModelCategory SSet.{0} := ordinaryJoyalModel
    letI : CategoryWithFibrations SSet.{0} :=
      ordinaryJoyalModel.categoryWithFibrations
    letI : CategoryWithWeakEquivalences SSet.{0} :=
      ordinaryJoyalModel.categoryWithWeakEquivalences
    letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
    letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
      simplicialReedyModelCategory SSet.{0}ᵒᵖ
    letI : IsFibrant (frame A).op := frame_op_isFibrant A
    letI : IsFibrant X := joyal_fibrant X
    letI : IsFibrant Y := joyal_fibrant Y
    have hweak : weakEquivalences SSet.{0} p := by
      change ordinaryJoyalModel.categoryWithWeakEquivalences.weakEquivalences p
      rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
      exact hp
    exact StrictFrameMappingTargetWeak.mapping_map_weak (frame A).op p hweak
  have hdiagram : weakEquivalences SSet.{0}
      (diagramHomPrecomp p.op (frame A).op) := by
    change weakEquivalences SSet.{0}
      ((StrictFrameMappingTargetWeak.mapping (frame A).op).map p)
    exact hnative
  have hpost : weakEquivalences SSet.{0} (mappingPost p A) :=
    ((weakEquivalences SSet.{0}).arrow_mk_iso_iff (postArrowIso p A)).1 hdiagram
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
    ((weakEquivalence_iff _).mpr hpost)

#print axioms postFunctor
#print axioms mappingPost_trivialFibration
#print axioms mappingPost_weak

end
end DaggerModels.PartII.OrdinaryJTMappingPostWeak
