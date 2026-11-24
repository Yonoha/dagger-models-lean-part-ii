import DaggerModelsPartII.DiagramTensorMappingAdjunction
import DaggerModelsPartII.RepresentableTensorAdjunction
import DaggerModelsPartII.DiagramMappingLimits
import DaggerModelsPartII.SegalRepresentables

/-! Enriched Yoneda for the literal diagram mapping space. -/

set_option autoImplicit false

open CategoryTheory Opposite

universe u

namespace DaggerModels.PartII

noncomputable section

/-- Mapping out of a simplicial representable is naturally evaluation. -/
def representableMappingIso {C : Type u} [SmallCategory C] (c : C) :
    diagramMappingTarget ((simplicialYoneda.{u, 0} C).obj c) ≅
      (evaluation Cᵒᵖ SSet.{u}).obj (op c) :=
  (diagramTensorMappingAdjunction ((simplicialYoneda.{u, 0} C).obj c)).rightAdjointUniq
    (representableTensorAdjunction c)

/-- The literal free reversal simplex has mapping space equal to the indicated value. -/
def daggerSimplexMappingIso (n : ℕ) (W : SegalLocalizers.ReverseDaggerSpace.{0}) :
    diagramMappingSpace (SegalLocalizers.daggerSimplex n) W ≅ W.obj (op ⟨n⟩) :=
  ((diagramMappingSource W).mapIso (SegalRepresentables.freeSimplexRepresentable n).op).symm ≪≫
    (representableMappingIso (C := ReverseSimplex) ⟨n⟩).app W

end

end DaggerModels.PartII
