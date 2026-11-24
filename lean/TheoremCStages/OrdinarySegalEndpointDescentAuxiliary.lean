import BisimplicialBaseSimplexKanFibers
import OrdinarySegalResolutionEquifibered
import OrdinarySegalVerticalPrecompletionUnitAudit

/-!
# The auxiliary descent fibration for the original endpoint resolution

All input maps are the original groupoid-simplex endpoint resolution maps.
The conclusion concerns the full comma-indexed auxiliary construction. Its
reconstruction as the original diagonal and the chosen-point comparison
remain separate proof obligations.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeReedyRelativeReplacement (relativeReplacement)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalEndpointDescentAuxiliary

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The exact auxiliary arrow of the original endpoint resolution. -/
def endpointAuxiliary (W : Space) : Arrow BiSSet.{0} :=
  BisimplicialBaseSimplexKanFibers.auxiliaryArrow
    (Arrow.mk (OrdinarySegalResolutionMappingFibers.endpointResolution W))

/-- The original Segal input supplies the auxiliary diagonal Kan fibration. -/
theorem endpoint_auxiliary_relative_diagonal_fibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    Fibration (DaggerNativeBisimplicialDiagonal.diagonalFunctor.map
      (relativeReplacement.obj (endpointAuxiliary W)).hom) :=
  BisimplicialBaseSimplexKanFibers.auxiliary_relative_diagonal_fibration
    (Arrow.mk (OrdinarySegalResolutionMappingFibers.endpointResolution W))
    (OrdinarySegalResolutionRelativeReedy.endpointResolution_row_fibration W)
    (OrdinarySegalResolutionEquifibered.endpointResolution_equifibered W hSegal)

/-- The same construction at precisely the original ordinary JT input. -/
theorem originalInput_auxiliary_relative_diagonal_fibration
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W) :
    Fibration (DaggerNativeBisimplicialDiagonal.diagonalFunctor.map
      (relativeReplacement.obj
        (endpointAuxiliary (RawOrdinaryJTQuillenTranspose.input W))).hom) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact endpoint_auxiliary_relative_diagonal_fibration
    (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal)

#print axioms endpoint_auxiliary_relative_diagonal_fibration
#print axioms originalInput_auxiliary_relative_diagonal_fibration

end

end DaggerModels.PartII.OrdinarySegalEndpointDescentAuxiliary
