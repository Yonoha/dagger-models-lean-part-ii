import DaggerModelsPartII.GroupoidSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The exact degree-zero value of the JT groupoid-simplex parameter

The native groupoid-completed zero simplex has one vertex. Its codiscrete nerve
is terminal in simplicial sets, so the parameter at zero is canonically
isomorphic to the actual standard zero simplex.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTParameterZero

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective

noncomputable section

private def codiscreteZeroIsTerminal :
    IsTerminal ((vertices ⋙ codiscreteNerve).obj ⦋0⦌) := by
  haveI : Subsingleton (vertices.obj ⦋0⦌) := by
    change Subsingleton (Fin 1)
    infer_instance
  haveI : Inhabited (vertices.obj ⦋0⦌) := by
    change Inhabited (Fin 1)
    infer_instance
  apply IsTerminal.ofUniqueHom
    (fun X => mapOfVertices X (fun _ => default))
  intro X f
  apply NatTrans.ext
  funext n s
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  exact Subsingleton.elim _ _

/-- The actual groupoid-completed zero simplex is terminal in simplicial sets. -/
def parameterZeroIsTerminal : IsTerminal (parameter.obj ⦋0⦌) :=
  IsTerminal.ofIso codiscreteZeroIsTerminal (parameterCodiscreteIso.app ⦋0⦌).symm

/-- The actual JT zero parameter is canonically isomorphic to the native
standard zero simplex. -/
def parameterZeroIso : parameter.obj ⦋0⦌ ≅ (Δ[0] : SSet.{0}) :=
  parameterZeroIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

/-- The isomorphism to the zero simplex uses its unique terminal map. -/
theorem parameterZeroIso_hom :
    parameterZeroIso.hom =
      SSet.stdSimplex.isTerminalObj₀.from (parameter.obj ⦋0⦌) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end

end DaggerModels.PartII.JTParameterZero
