import RawOrdinaryJTUnitCSSWeak
import DaggerModelsPartII.JTRawOrdinaryAdjoint

/-!
# Strict endpoint calibration for the actual raw JT transpose

The ordinary CSS morphism proved weak in `RawOrdinaryJTUnitCSSWeak` has
the original raw rows and the original ordered endpoint operators. These
equalities only unfold currying. They preserve the exact selected points
and the original chosen-fiber map defined in `JTRawOrdinaryAdjoint`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.RawOrdinaryJTEndpointCalibration

open RawOrdinaryJTQuillenTranspose (input)
open OrdinaryJTCurriedAdjunction (right)
open JTProjectiveOrderedFiberComparison (row endpoint)
open JTRightAdjointOrderedFiber
open JTRawOrdinaryAdjoint

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The input's literal horizontal component is the source row of the
original ordered endpoint arrow. -/
theorem input_row (W : Source) (m : SimplexCategory) :
    (input W).obj (op m) = row W m := rfl

/-- The right adjoint's literal horizontal component is the original
ordinary target row, with the same native universe lift. -/
theorem target_row (S : SSet.{0}) (m : SimplexCategory) :
    (right.obj S).obj (op m) = ordinaryRow S m := rfl

/-- Each component of the CSS-weak raw transpose is precisely the original
`gRawRow`, for every horizontal degree and the complete vertical row. -/
theorem transpose_row (W : Source) (m : SimplexCategory) :
    (JTRealizationDiagonal.ordinaryCurry.map (gRawTilde W)).app (op m) =
      gRawRow W m := rfl

/-- The source's two ordered outer cofaces are the original endpoints. -/
theorem input_endpoint (W : Source) (i : Fin 2) :
    (input W).map (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op =
      endpoint W i := rfl

/-- The target's two ordered outer cofaces are the original endpoints. -/
theorem target_endpoint (S : SSet.{0}) (i : Fin 2) :
    (right.obj S).map (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op =
      ordinaryRowEndpoint S i := rfl

#print axioms input_row
#print axioms target_row
#print axioms transpose_row
#print axioms input_endpoint
#print axioms target_endpoint

end

end DaggerModels.PartII.RawOrdinaryJTEndpointCalibration
