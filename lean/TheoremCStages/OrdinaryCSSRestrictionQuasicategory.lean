import OrdinaryCSSHorizontalRestrictions
import DaggerModelsPartII.DiagramRestrictionLimits

/-!
# Quasicategories from arbitrary vertical restrictions of a CSS object

The empty vertical restriction is terminal because the actual restriction
functor is a right adjoint. Inner lifting for the empty-to-K restriction
then gives a quasicategory for every original vertical simplicial set K.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryCSSRestrictionQuasicategory

noncomputable section

/-- The empty vertical restriction is the actual terminal horizontal object. -/
def emptyRestriction_terminal (W : OrdinaryCSSLocalization.Space) :
    IsTerminal (diagramRestriction (⊥_ SSet.{0}) W.flip) := by
  let F := diagramRestrictionFunctor W.flip
  letI : PreservesLimitsOfSize.{0, 0} F :=
    (diagramRestrictionAdjunction W.flip).rightAdjoint_preservesLimits
  exact (terminalOpOfInitial
    (initialIsInitial : IsInitial (⊥_ SSet.{0}))).isTerminalObj F (op (⊥_ SSet.{0}))

/-- Every vertical limit restriction of a CSS-fibrant ordinary simplicial
space is a quasicategory, including the actual matching-boundary target. -/
theorem restriction_quasicategory (W : OrdinaryCSSLocalization.Space)
    (hW : @HomotopicalAlgebra.IsFibrant OrdinaryCSSLocalization.Space _
      OrdinaryCSSLocalization.model.categoryWithFibrations _ W)
    (K : SSet.{0}) : SSet.Quasicategory (diagramRestriction K W.flip) := by
  let v : (⊥_ SSet.{0}) ⟶ K := initial.to K
  haveI : Mono v := inferInstance
  exact (DaggerNativeInnerHornFactorization.quasicategory_iff_inner_terminal
    (diagramRestrictionPre v W.flip) (emptyRestriction_terminal W)).mpr
      (OrdinaryCSSHorizontalRestrictions.restriction_innerFibration W hW v)

#print axioms emptyRestriction_terminal
#print axioms restriction_quasicategory

end
end DaggerModels.PartII.OrdinaryCSSRestrictionQuasicategory
