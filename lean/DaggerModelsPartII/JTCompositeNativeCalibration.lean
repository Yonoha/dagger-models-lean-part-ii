import DaggerModelsPartII.JTRightAdjointNativeRow
import DaggerModelsPartII.JTCoendMateFormula
import DaggerModelsPartII.JTXiRowEndpoints

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open OrdinaryRigidification.DaggerRigidification
open OrdinaryRigidification.DaggerNerve

namespace DaggerModels.PartII.JTCompositeNativeCalibration

open DaggerJTAdjunction JTCoendMate JTCoendMateFormula
open JTRightAdjointOrderedFibersCore

noncomputable section

/-- On every represented pair, the composite adjunction's generator
equivalence is the native Xi Hom map, with only the Yoneda universe lift. -/
theorem compositeGeneratorEquiv_eq_native (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) (k : SimplexCategory)
    (f : RigidifiedJTFrames.Xi.obj (m, k) ⟶ C) :
    compositeGeneratorEquiv C (m, k) f =
      ULift.up (DaggerActualRigidificationQuillen.adjunction.homEquiv
        (frame.obj (m, k)) C f) := by
  change daggerGeneratorEquiv (daggerCoherentNerve.obj C) m k
      (DaggerActualRigidificationQuillen.adjunction.homEquiv
        (frame.obj (m, k)) C f) = _
  exact JTRightAdjointNativeRow.daggerGeneratorEquiv_eq_native _ m k _

/-- The inverse of the existing Xi row comparison is precisely the
original composite represented-generator equivalence. -/
theorem xiRowMappingIso_inv (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) (k : SimplexCategory)
    (f : RigidifiedJTFrames.Xi.obj (m, k) ⟶ C) :
    ((JTXiRowEndpoints.xiRowMappingIso C m).inv.app (op k)) f =
      compositeGeneratorEquiv C (m, k) f := by
  change ULift.up (DaggerActualRigidificationQuillen.adjunction.homEquiv
    (frame.obj (m, k)) C f) = _
  exact (compositeGeneratorEquiv_eq_native C m k f).symm

end

end DaggerModels.PartII.JTCompositeNativeCalibration
