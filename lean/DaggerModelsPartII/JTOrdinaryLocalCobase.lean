import DaggerModelsPartII.OrdinaryCofibrationLocalComparison
import DaggerModelsPartII.JTXiOrdinaryLatching
import DaggerModelsPartII.JTForgottenFrameCofibrancy

/-!
# Universal local cobase properties of the actual forgotten JT frames

The actual ordinary Xi and forgotten Gamma cosimplicial latching maps belong
to the newly proved universal ordinary local class. This applies to the
original full reversal-index frames and their native opposite matching maps.
It does not assert the general coend Lambda weak comparison.
-/

set_option autoImplicit false

open CategoryTheory Simplicial DaggerModels
open DaggerModels.OrdinaryUniversalLocalCobase

namespace DaggerModels.PartII.JTOrdinaryLocalCobase

noncomputable section

private local instance : CategoryTheory.Limits.HasColimits SimplicialCat.{0, 0} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits
private local instance : CategoryTheory.Limits.HasLimits SimplicialCat.{0, 0}ᵒᵖ :=
  inferInstance

/-- Every actual forgotten Xi latching map has universal Hom monicity and
preserves the local geometric comparison under every supplied cobase. -/
theorem actual_Xi_matching_in_U (m : ReverseSimplex) (n : ℕ) :
    U (((matchingComparison n).app (JTXiOrdinaryLatching.actualOrdinaryXi m).op).unop) :=
  OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_U _
    (JTXiOrdinaryLatching.actualOrdinaryXi_matching_cofibration m n)

/-- The actual ordinary matching comparison of forgotten Gamma has the
same universal local property, in every degree and full reversal index. -/
theorem actual_Gamma_matching_in_U (m : ReverseSimplex) (n : ℕ) :
    U (((matchingComparison n).app
      ((JTRelativeReedyFrame.GammaOuter.obj m ⋙ DaggerSimplicialCat.forget).op)).unop) :=
  OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_U _
    (JTForgottenFrameCofibrancy.forgotten_Gamma_ordinary_matching_cofibration m n)

end

end DaggerModels.PartII.JTOrdinaryLocalCobase
