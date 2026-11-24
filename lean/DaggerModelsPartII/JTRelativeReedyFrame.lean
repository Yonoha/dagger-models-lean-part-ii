import DaggerModelsPartII.RigidifiedJTFrames
import DaggerModelsPartII.ReedyZeroFixedFactorization
import DaggerModels.DaggerSmallObject
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The actual full-outer JT frame before coefficient-change verification

The entire reversal-simplex index is kept inside the coefficient functor
category. A degree-zero-fixed relative Reedy factorization in the opposite
category therefore constructs one cosimplicial diagram natural in every
reversal-simplex morphism.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty DaggerModels

namespace DaggerModels.PartII.JTRelativeReedyFrame

open RigidifiedJTFrames

noncomputable section

abbrev Coefficient := DaggerSimplicialCat.{0, 0}
abbrev OuterDiagram := ReverseSimplex ⥤ Coefficient
abbrev OppositeOuterDiagram := OuterDiagramᵒᵖ

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits

/-- Cofibrations detected at every outer reversal-simplex index. -/
def outerCofibrations : MorphismProperty OuterDiagram :=
  (DaggerGeneratingCofibrations.generators.{0}.rlp.llp).functorCategory ReverseSimplex

/-- Trivial fibrations detected at every outer reversal-simplex index. -/
def outerTrivialFibrations : MorphismProperty OuterDiagram :=
  (DaggerGeneratingCofibrations.generators.{0}.rlp).functorCategory ReverseSimplex

/-- The left class after taking opposite categories. -/
def leftClass : MorphismProperty OppositeOuterDiagram := outerTrivialFibrations.op

/-- The right class after taking opposite categories. -/
def rightClass : MorphismProperty OppositeOuterDiagram := outerCofibrations.op

private local instance : outerCofibrations.HasFactorization outerTrivialFibrations := by
  let d := DaggerSmallObject.generators_functorialFactorizationData.{0}
  letI : outerCofibrations.HasFunctorialFactorization outerTrivialFibrations :=
    ⟨⟨d.functorCategory ReverseSimplex⟩⟩
  infer_instance

private local instance : leftClass.HasFactorization rightClass := by
  change outerTrivialFibrations.op.HasFactorization outerCofibrations.op
  infer_instance

/-- Rigidified JT generators, curried with the ordinary simplex index first. -/
def XiCurried : SimplexCategory ⥤ OuterDiagram :=
  (Functor.curry.obj Xi).flip

/-- The same full-outer diagram in the opposite coefficient category. -/
def XiOpposite : SimplexCategoryᵒᵖ ⥤ OppositeOuterDiagram :=
  XiCurried.op

/-- Factor the terminal map without changing its degree-zero source. -/
def XiTerminalMap : XiOpposite ⟶
    (⊤_ (SimplexCategoryᵒᵖ ⥤ OppositeOuterDiagram)) :=
  terminal.from XiOpposite

/-- The complete outer-natural Reedy middle diagram in opposite form. -/
def GammaOpposite : SimplexCategoryᵒᵖ ⥤ OppositeOuterDiagram :=
  zeroFixedReedyMid XiTerminalMap leftClass rightClass

/-- The factor that becomes the frame comparison after taking opposites. -/
def comparisonOpposite : XiOpposite ⟶ GammaOpposite :=
  zeroFixedReedyLeft XiTerminalMap leftClass rightClass

/-- The right factor witnesses the Reedy fibrancy condition after its
coefficient-class hypotheses are established. -/
def terminalProjectionOpposite : GammaOpposite ⟶
    (⊤_ (SimplexCategoryᵒᵖ ⥤ OppositeOuterDiagram)) :=
  zeroFixedReedyRight XiTerminalMap leftClass rightClass

/-- A cosimplicial object in the entire outer diagram category. -/
def Gamma : SimplexCategory ⥤ OuterDiagram := GammaOpposite.unop

/-- The frame comparison is natural in every reversal-simplex morphism. -/
def comparison : Gamma ⟶ XiCurried :=
  NatTrans.unop comparisonOpposite ≫ (Functor.opUnopIso XiCurried).hom

/-- Reindex the same frame as an outer diagram of cosimplicial objects. -/
def GammaOuter : ReverseSimplex ⥤ SimplexCategory ⥤ Coefficient := Gamma.flip

/-- The same comparison, with reversal-simplex index outermost. -/
def comparisonOuter : GammaOuter ⟶ XiCurried.flip :=
  (flipFunctor SimplexCategory ReverseSimplex Coefficient).map comparison

/-- The zero-degree middle object is the original represented frame. -/
theorem GammaOpposite_zero :
    GammaOpposite.obj (op ⦋0⦌) = XiOpposite.obj (op ⦋0⦌) :=
  zeroFixedReedyMid_obj_zero XiTerminalMap leftClass rightClass

/-- The original factor in opposite form is the identity at degree zero. -/
theorem comparisonOpposite_zero :
    comparisonOpposite.app (op ⦋0⦌) =
      𝟙 (XiOpposite.obj (op ⦋0⦌)) :=
  zeroFixedReedyLeft_app_zero XiTerminalMap leftClass rightClass

/-- Before the separate identification with `A`, the actual cosimplicial
comparison is literally the identity in degree zero. -/
theorem comparison_zero :
    comparison.app ⦋0⦌ = 𝟙 (XiCurried.obj ⦋0⦌) := rfl

end

end DaggerModels.PartII.JTRelativeReedyFrame
