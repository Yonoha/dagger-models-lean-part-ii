import OrdinaryJTMappingKan
import OrdinaryJTRightNerveSegal

/-!
# Kan complexes in the literal ordinary JT right-nerve rows

Transport the checked Kan property along the actual native row/Hom isomorphism.
No replacement of the ordinary target or of the right adjoint is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTRightNerveKan

noncomputable section

/-- Every literal row of the ordinary JT right nerve of a quasicategory is Kan. -/
theorem ordinaryRow_kan (X : SSet.{0}) [X.Quasicategory] (m : SimplexCategory) :
    (JTRightAdjointOrderedFiber.ordinaryRow X m).KanComplex := by
  letI : (OrdinaryJTMappingFrameWeak.mapping X (SSet.stdSimplex.obj m)).KanComplex :=
    OrdinaryJTMappingKan.mapping_kan X (SSet.stdSimplex.obj m)
  apply (isFibrant_iff_of_isTerminal
    ((OrdinaryJTRightNerveSegal.rowMappingIso X m).hom ≫ terminal.from _)
    terminalIsTerminal).mpr
  infer_instance

#print axioms ordinaryRow_kan

end
end DaggerModels.PartII.OrdinaryJTRightNerveKan
