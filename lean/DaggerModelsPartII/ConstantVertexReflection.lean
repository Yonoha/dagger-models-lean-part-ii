import DaggerModelsPartII.ConstantVertexQuillenFromLocalWeak
import DaggerModelsPartII.CosimplicialQuillenComparison
import DaggerModelsPartII.DiagramMappingRepresentable
import DaggerModelsPartII.InjectiveStandardFrame
import DaggerModelsPartII.ResolutionGeneratorCofibrancy

/-! Vertex evaluation reflects weak equivalences between injective-local fibrant objects
once the literal constant-vertex adjunction is Quillen. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.ConstantVertexAdjunction

open SegalLocalizers

noncomputable section

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerOriginalJoyalModel.standardModelCategory.{0}
private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
private local instance : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos ReverseSimplexᵒᵖ) :=
  ⟨InjectiveKanDiagram.generatorsAreAllMonos ReverseSimplexᵒᵖ⟩
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ ReverseDaggerSpace.{0}ᵒᵖ) :=
  simplicialReedyModelCategory ReverseDaggerSpace.{0}ᵒᵖ

private theorem injectiveWeak_is_segalWeak {X Y : ReverseDaggerSpace.{0}} (f : X ⟶ Y)
    (hf : (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithWeakEquivalences.weakEquivalences f) :
    weakEquivalences ReverseDaggerSpace.{0} f := by
  change injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences f
  rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).2]
  letI : ModelCategory ReverseDaggerSpace.{0} := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  exact Localization.weakEquivalences_le_localEquivalences _ f hf

private theorem standardFrame_isFibrant (A : ReverseDaggerSpace.{0}) :
    IsFibrant (InjectiveKanDiagram.standardFrame ReverseSimplexᵒᵖ A) := by
  let E := InjectiveKanDiagram.standardFrame ReverseSimplexᵒᵖ A
  have h (n : ℕ) :
      (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations
        ((matchingComparison n).app E).unop := by
    letI : ModelCategory ReverseDaggerSpace.{0} := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ ReverseDaggerSpace.{0}ᵒᵖ) :=
      simplicialReedyModelCategory ReverseDaggerSpace.{0}ᵒᵖ
    have h := (reedyFibrant_iff_matchingComparison E).mp
      (InjectiveKanDiagram.standardFrame_reedyFibrant ReverseSimplexᵒᵖ A) n
    rw [fibrations_op] at h
    exact h
  apply (reedyFibrant_iff_matchingComparison E).mpr
  intro n
  rw [fibrations_op]
  change injectiveSegalModel.categoryWithCofibrations.cofibrations ((matchingComparison n).app E).unop
  rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).1]
  exact h n

private theorem standardAugmentation_isWeak (A : ReverseDaggerSpace.{0}) :
    weakEquivalences _ (InjectiveKanDiagram.standardAugmentation ReverseSimplexᵒᵖ A) := by
  intro n
  change weakEquivalences ReverseDaggerSpace.{0}ᵒᵖ
    ((InjectiveKanDiagram.diagramTensorProjection ReverseSimplexᵒᵖ A
      (SSet.stdSimplex.obj n.unop)).op)
  rw [weakEquivalences_op]
  exact injectiveWeak_is_segalWeak _
    (InjectiveKanDiagram.diagramTensorProjection_weak ReverseSimplexᵒᵖ A n.unop.len)

private theorem vertex_isFibrant [adjunction.{0}.IsQuillenAdjunction]
    (Z : ReverseDaggerSpace.{0}) [IsFibrant Z] : IsFibrant (vertex.obj Z) := by
  letI := Adjunction.IsQuillenAdjunction.preservesFibrations adjunction.{0}
  letI := adjunction.{0}.rightAdjoint_preservesLimits
  have hT : IsTerminal (vertex.obj (⊤_ ReverseDaggerSpace.{0})) :=
    terminalIsTerminal.isTerminalObj vertex _
  exact (isFibrant_iff_of_isTerminal (vertex.map (terminal.from Z)) hT).mpr inferInstance

private def standardFrameMappingTargetIso (A : ReverseDaggerSpace.{0}) :
    oppositeFrameMappingTarget (InjectiveKanDiagram.standardFrame ReverseSimplexᵒᵖ A) ≅
      diagramMappingTarget A :=
  NatIso.ofComponents
    (InjectiveKanDiagram.standardFrameMappingIso ReverseSimplexᵒᵖ A) (by
      intro Z Z' f
      ext n x : 2
      rfl)

private def freeSimplexMappingTargetIso (n : ℕ) :
    diagramMappingTarget (daggerSimplex n) ≅
      (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op ⟨n⟩) := by
  let e := SegalRepresentables.freeSimplexRepresentable n
  let e₁ : diagramMappingTarget _ ≅ diagramMappingTarget (daggerSimplex n) :=
    NatIso.ofComponents (fun Z ↦ (diagramMappingSource Z).mapIso e.op) (by
      intro Z Z' f
      ext k x : 2
      change ((Functor.whiskerRight e.hom _ ≫ x) ≫ f) =
        Functor.whiskerRight e.hom _ ≫ (x ≫ f)
      exact Category.assoc _ _ _)
  exact e₁.symm ≪≫ representableMappingIso (C := ReverseSimplex) ⟨n⟩

/-- Each row is Kan weak if its vertex-evaluation map is dagger Joyal weak. -/
theorem row_weak_of_vertex_weak [adjunction.{0}.IsQuillenAdjunction]
    {Z Z' : ReverseDaggerSpace.{0}} [IsFibrant Z] [IsFibrant Z']
    (f : Z ⟶ Z') (hf : weakEquivalences DaggerSSet.{0} (vertex.map f))
    (m : ReverseSimplexᵒᵖ) : weakEquivalences SSet.{0} (f.app m) := by
  let n := m.unop.len
  have hm : op (⟨n⟩ : ReverseSimplex) = m := rfl
  rw [← hm]
  let A := freeDagger.obj (SSet.stdSimplex.obj ⦋n⦌ : SSet.{0})
  letI : IsCofibrant A := freeDagger_isCofibrant _
  letI : IsFibrant (vertex.obj Z) := vertex_isFibrant Z
  letI : IsFibrant (vertex.obj Z') := vertex_isFibrant Z'
  let E := InjectiveKanDiagram.standardFrame ReverseSimplexᵒᵖ (daggerSimplex n)
  letI : IsFibrant E := standardFrame_isFibrant _
  have h := oppositeFrameMappingTarget_weak_of_rightAdjoint_weak adjunction.{0} (A := A)
    (InjectiveKanDiagram.standardAugmentation ReverseSimplexᵒᵖ (daggerSimplex n))
    (standardAugmentation_isWeak _) f hf
  let e := standardFrameMappingTargetIso (daggerSimplex n) ≪≫ freeSimplexMappingTargetIso n
  change weakEquivalences SSet.{0} (((evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op ⟨n⟩)).map f)
  apply ((weakEquivalences SSet.{0}).cancel_left_of_respectsIso (e.hom.app Z) _).mp
  rw [← e.hom.naturality f]
  exact ((weakEquivalences SSet.{0}).cancel_right_of_respectsIso _ (e.hom.app Z')).mpr h

/-- The original right adjoint reflects weak equivalences between fibrant objects of the
injective Segal model whenever the constant-vertex adjunction is Quillen. -/
theorem vertex_reflects_weak_between_fibrant [adjunction.{0}.IsQuillenAdjunction]
    {Z Z' : ReverseDaggerSpace.{0}} [IsFibrant Z] [IsFibrant Z']
    (f : Z ⟶ Z') (hf : weakEquivalences DaggerSSet.{0} (vertex.map f)) :
    weakEquivalences ReverseDaggerSpace.{0} f := by
  apply injectiveWeak_is_segalWeak
  letI : ModelCategory ReverseDaggerSpace.{0} := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  change weakEquivalences ReverseDaggerSpace.{0} f
  rw [InjectiveKanDiagram.model_weakEquivalences]
  intro m
  exact row_weak_of_vertex_weak f hf m

end

end DaggerModels.PartII.ConstantVertexAdjunction
