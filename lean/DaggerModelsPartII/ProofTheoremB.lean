import DaggerModelsPartII.FullTheoremBStatement
import DaggerModelsPartII.TheoremBCore
import DaggerModelsPartII.DiagramSimplicialEnrichment

/-! Theorem B with the actual localized models and literal simplicial structure. -/

set_option autoImplicit false

namespace DaggerModels.PartII

open SegalLocalizers InjectiveKanDiagram DiagramCotensor

noncomputable section

/-- The native enrichment, normalized on ordinary morphisms, and the literal
parameterized tensor and cotensor with their natural exponential laws. -/
def theoremBSimplicialStructure : FullTheoremBStatement.LiteralSimplicialStructure where
  enrichment := DiagramSimplicialEnrichment.diagramSimplicialCategory ReverseSimplexᵒᵖ
  homComparison := DiagramSimplicialEnrichment.homComparison ReverseSimplexᵒᵖ
  homComparison_ordinary := by
    intro A B f
    exact DiagramSimplicialEnrichment.homComparison_ordinary ReverseSimplexᵒᵖ f
  tensorMappingAdjunction := diagramParametrizedAdjunction ReverseSimplexᵒᵖ
  tensorCotensorAdjunction := parametrizedTensorCotensorAdjunction
  tensorExponential := diagramMappingTensorIso ReverseSimplexᵒᵖ
  cotensorExponential := diagramMappingCotensorIso
  tensorExponential_precomp := fun i K W ↦
    diagramMappingTensorIso_precomp ReverseSimplexᵒᵖ i K W
  tensorExponential_parameter := by
    intro A K L j W
    exact diagramMappingTensorIso_tensorMap ReverseSimplexᵒᵖ A j W
  cotensorExponential_precomp := fun i K W ↦ mappingCotensorIso_precomp i W K
  cotensorExponential_parameter := by
    intro A K L j W
    exact mappingCotensorIso_parameter A W j

/-- Theorem B of Models for dagger categories II, at simplicial-set universe zero. -/
theorem theoremB : FullTheoremBStatement.fullStatement :=
  ⟨theoremB_core, ⟨theoremBSimplicialStructure⟩⟩

end

end DaggerModels.PartII
