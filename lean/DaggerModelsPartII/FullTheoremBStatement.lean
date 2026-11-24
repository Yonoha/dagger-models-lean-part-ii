import DaggerModelsPartII.TheoremBStatement
import DaggerModelsPartII.DiagramCotensor
import DaggerModelsPartII.DiagramMappingTensor
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
# Theorem B with the full literal simplicial structure

The earlier seven-clause statement is retained verbatim. The additional data
fix an ordinary simplicial enrichment and compare its Hom bifunctor naturally
with the manuscript's literal mapping spaces. The tensor and cotensor refer
to the same mapping spaces and satisfy their internal-Hom exponential laws.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite

namespace DaggerModels.PartII.FullTheoremBStatement

open SegalLocalizers InjectiveKanDiagram DiagramCotensor

noncomputable section

/-- The literal tensor by the simplicial unit is the original diagram,
with the pointwise right unitor as its specified comparison. -/
def tensorUnitIso (A : ReverseDaggerSpace.{0}) :
    (diagramTensor A).obj (𝟙_ SSet.{0}) ≅ A :=
  NatIso.ofComponents (fun c ↦ ρ_ (A.obj c)) (by
    intro c d f
    exact rightUnitor_naturality (A.map f))

/-- Structural data for the manuscript's literal simplicial mapping spaces.
The native enriched-category fields include identity, composition and all
unit and associativity laws, together with the ordinary Hom comparison. -/
structure LiteralSimplicialStructure where
  enrichment : SimplicialCategory ReverseDaggerSpace.{0}
  homComparison : letI := enrichment;
    SimplicialCategory.sHomFunctor ReverseDaggerSpace.{0} ≅
      InjectiveKanDiagram.diagramMappingSource ReverseSimplexᵒᵖ
  homComparison_ordinary : letI := enrichment;
    ∀ {A B : ReverseDaggerSpace.{0}} (f : A ⟶ B),
      eHomEquiv SSet f ≫ (homComparison.hom.app (op A)).app B =
        (diagramTensorMappingAdjunction A).homEquiv (𝟙_ SSet.{0}) B
          ((tensorUnitIso A).hom ≫ f)
  tensorMappingAdjunction :
    curriedDiagramTensor ReverseSimplexᵒᵖ ⊣₂
      InjectiveKanDiagram.diagramMappingSource ReverseSimplexᵒᵖ
  tensorCotensorAdjunction :
    (curriedDiagramTensor ReverseSimplexᵒᵖ).flip ⊣₂ diagramCotensor
  tensorExponential (A : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    diagramMappingTarget ((diagramTensor A).obj K) ≅
      diagramMappingTarget A ⋙ ihom K
  cotensorExponential (A : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    diagramCotensor.obj (op K) ⋙ diagramMappingTarget A ≅
      diagramMappingTarget A ⋙ ihom K

  tensorExponential_precomp :
    ∀ {A B : ReverseDaggerSpace.{0}} (i : A ⟶ B) (K : SSet.{0})
      (W : ReverseDaggerSpace.{0}),
      diagramMappingPrecomp (((curriedDiagramTensor ReverseSimplexᵒᵖ).map i).app K) W ≫
          (tensorExponential A K).hom.app W =
        (tensorExponential B K).hom.app W ≫
          (ihom K).map (diagramMappingPrecomp i W)
  tensorExponential_parameter :
    ∀ (A : ReverseDaggerSpace.{0}) {K L : SSet.{0}} (j : K ⟶ L)
      (W : ReverseDaggerSpace.{0}),
      diagramMappingPrecomp ((diagramTensor A).map j) W ≫
          (tensorExponential A K).hom.app W =
        (tensorExponential A L).hom.app W ≫
          (MonoidalClosed.pre j).app (diagramMappingSpace A W)
  cotensorExponential_precomp :
    ∀ {A B : ReverseDaggerSpace.{0}} (i : A ⟶ B) (K : SSet.{0})
      (W : ReverseDaggerSpace.{0}),
      diagramMappingPrecomp i ((diagramCotensor.obj (op K)).obj W) ≫
          (cotensorExponential A K).hom.app W =
        (cotensorExponential B K).hom.app W ≫
          (ihom K).map (diagramMappingPrecomp i W)
  cotensorExponential_parameter :
    ∀ (A : ReverseDaggerSpace.{0}) {K L : SSet.{0}} (j : K ⟶ L)
      (W : ReverseDaggerSpace.{0}),
      diagramMappingPostcomp A ((diagramCotensor.map j.op).app W) ≫
          (cotensorExponential A K).hom.app W =
        (cotensorExponential A L).hom.app W ≫
          (MonoidalClosed.pre j).app (diagramMappingSpace A W)

/-- The seven model-theoretic clauses together with a coherent simplicial
structure using exactly the stated tensor, cotensor and mapping spaces. -/
def fullStatement : Prop :=
  TheoremBStatement.statement ∧ Nonempty LiteralSimplicialStructure

end

end DaggerModels.PartII.FullTheoremBStatement
