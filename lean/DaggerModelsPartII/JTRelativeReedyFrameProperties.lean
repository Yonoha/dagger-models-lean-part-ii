import DaggerModelsPartII.JTRelativeReedyFrame
import DaggerModelsPartII.ReedyCoefficientChange
import ActualDaggerRigidificationQuillen
import DaggerModelsPartII.ReedyFibrantDiagrams
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Model-class properties of the actual full-outer JT frame

The factorization is carried out in the category of all reversal-simplex
diagrams. Its classes are identified pointwise with the actual Bergner
trivial fibrations and cofibrations.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite Simplicial MorphismProperty
open DaggerModels DaggerModels.PartII DaggerModels.PartII.RigidifiedJTFrames

namespace DaggerModels.PartII.JTRelativeReedyFrame

noncomputable section

private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) :=
  simplicialReedyModelCategory Coefficientᵒᵖ

/-- Pointwise morphism properties inherit stability under isomorphisms. -/
private instance pointwiseRespectsIso (P : MorphismProperty Coefficient)
    [P.RespectsIso] : (P.functorCategory ReverseSimplex).RespectsIso where
  precomp i hi f hf j := by
    letI : IsIso i := hi
    exact RespectsIso.precomp P (i.app j) (f.app j) (hf j)
  postcomp i hi f hf j := by
    letI : IsIso i := hi
    exact RespectsIso.postcomp P (i.app j) (f.app j) (hf j)

/-- Pointwise morphism properties inherit identity arrows. -/
private instance pointwiseContainsIdentities (P : MorphismProperty Coefficient)
    [P.ContainsIdentities] : (P.functorCategory ReverseSimplex).ContainsIdentities where
  id_mem F j := P.id_mem (F.obj j)

/-- The generating lifting class is precisely the actual trivial-fibration
class of the Bergner-type dagger model. -/
theorem generators_rlp_eq_trivialFibrations :
    DaggerGeneratingCofibrations.generators.{0}.rlp =
      trivialFibrations Coefficient := by
  calc
    DaggerGeneratingCofibrations.generators.{0}.rlp =
        DaggerGeneratingCofibrations.generators.{0}.rlp.llp.rlp :=
      (rlp_llp_rlp _).symm
    _ = (cofibrations Coefficient).rlp := by
      rw [DaggerActualRigidificationQuillen.target_cof]
    _ = trivialFibrations Coefficient :=
      rlp_eq_of_wfs (cofibrations Coefficient) (trivialFibrations Coefficient)

/-- The two outer classes are actual pointwise model classes. -/
theorem outerCofibrations_eq :
    outerCofibrations = (cofibrations Coefficient).functorCategory ReverseSimplex := by
  unfold outerCofibrations
  rw [DaggerActualRigidificationQuillen.target_cof]

theorem outerTrivialFibrations_eq :
    outerTrivialFibrations =
      (trivialFibrations Coefficient).functorCategory ReverseSimplex := by
  unfold outerTrivialFibrations
  rw [generators_rlp_eq_trivialFibrations]

private local instance : leftClass.RespectsIso := by
  rw [leftClass, outerTrivialFibrations_eq]
  infer_instance

private local instance : rightClass.RespectsIso := by
  rw [rightClass, outerCofibrations_eq]
  infer_instance

private local instance : leftClass.ContainsIdentities := by
  rw [leftClass, outerTrivialFibrations_eq]
  infer_instance

private local instance : outerCofibrations.HasFactorization outerTrivialFibrations := by
  let d := DaggerSmallObject.generators_functorialFactorizationData.{0}
  letI : outerCofibrations.HasFunctorialFactorization outerTrivialFibrations :=
    ⟨⟨d.functorCategory ReverseSimplex⟩⟩
  infer_instance

private local instance : leftClass.HasFactorization rightClass := by
  change outerTrivialFibrations.op.HasFactorization outerCofibrations.op
  infer_instance

/-- Every relative latching map of the outer-natural opposite comparison
belongs to the pointwise trivial-fibration class after taking opposites. -/
theorem comparisonOpposite_relativeLatching (n : ℕ) :
    leftClass (relativeLatchingMap n comparisonOpposite) :=
  zeroFixedReedyLeft_relative_mem_of_id XiTerminalMap leftClass rightClass n

/-- The zero component of the rigidified represented frame is cofibrant
at every outer index. -/
private theorem XiCurried_zero_isCofibrant (m : ReverseSimplex) :
    IsCofibrant ((XiCurried.obj ⦋0⦌).obj m) := by
  change IsCofibrant (Xi.obj (m, ⦋0⦌))
  let e := XiZeroIso.app m
  letI : IsCofibrant (A.obj m) := A_isCofibrant m
  letI : Cofibration e.inv := inferInstance
  exact isCofibrant_of_cofibration e.inv

/-- Evaluation at degree zero of the terminal opposite outer diagram is
initial in the ordinary outer diagram category. -/
private def terminalZero_isInitial :
    IsInitial (((⊤_ (SimplexCategoryᵒᵖ ⥤ OppositeOuterDiagram)).obj
      (op ⦋0⦌)).unop) := by
  exact initialUnopOfTerminal
    (terminalIsTerminal.isTerminalObj
      ((evaluation SimplexCategoryᵒᵖ OppositeOuterDiagram).obj (op ⦋0⦌)) _)

/-- The terminal map at degree zero belongs to the chosen right class,
using the actual cofibrancy of the rigidified reversal simplices. -/
theorem XiTerminalMap_zero_rightClass :
    rightClass (XiTerminalMap.app (op ⦋0⦌)) := by
  change outerCofibrations (XiTerminalMap.app (op ⦋0⦌)).unop
  rw [outerCofibrations_eq]
  intro m
  have hcof : IsCofibrant ((Opposite.unop (XiOpposite.obj (op ⦋0⦌))).obj m) := by
    change IsCofibrant ((XiCurried.obj ⦋0⦌).obj m)
    exact XiCurried_zero_isCofibrant m
  let hinit : IsInitial (((⊤_ (SimplexCategoryᵒᵖ ⥤ OppositeOuterDiagram)).obj
      (op ⦋0⦌)).unop.obj m) :=
    terminalZero_isInitial.isInitialObj
      ((evaluation ReverseSimplex Coefficient).obj m) _
  exact (cofibration_iff _).1
    ((isCofibrant_iff_of_isInitial _ hinit).mp hcof)

/-- Every relative matching map of the completed frame belongs to the
pointwise opposite cofibration class. -/
theorem terminalProjectionOpposite_relativeMatching (n : ℕ) :
    rightClass (relativeMatchingMap n terminalProjectionOpposite) :=
  zeroFixedReedyRight_relative_mem XiTerminalMap leftClass rightClass
    XiTerminalMap_zero_rightClass n

/-- Opposite evaluation retains every reversal-simplex component. -/
def evaluationOpposite (m : ReverseSimplex) :
    OppositeOuterDiagram ⥤ Coefficientᵒᵖ :=
  ((evaluation ReverseSimplex Coefficient).obj m).op

private local instance (m : ReverseSimplex) :
    PreservesLimitsOfSize.{0, 0} (evaluationOpposite m) := by
  dsimp [evaluationOpposite]
  letI : PreservesColimitsOfSize.{0, 0}
      ((evaluation ReverseSimplex Coefficient).obj m) :=
    ⟨fun {_} _ => inferInstance⟩
  exact preservesLimitsOfSize_op _

private local instance (m : ReverseSimplex) :
    PreservesColimitsOfSize.{0, 0} (evaluationOpposite m) := by
  dsimp [evaluationOpposite]
  letI : PreservesLimitsOfSize.{0, 0}
      ((evaluation ReverseSimplex Coefficient).obj m) :=
    ⟨fun {_} _ => inferInstance⟩
  exact preservesColimitsOfSize_op _

/-- The right class becomes the literal fibration class after evaluating
an outer reversal-simplex object and taking opposites. -/
private theorem evaluationOpposite_rightClass (m : ReverseSimplex)
    {X Y : OppositeOuterDiagram} (f : X ⟶ Y) (hf : rightClass f) :
    fibrations Coefficientᵒᵖ ((evaluationOpposite m).map f) := by
  rw [fibrations_op]
  change (cofibrations Coefficient) (f.unop.app m)
  change outerCofibrations f.unop at hf
  rw [outerCofibrations_eq] at hf
  exact hf m

/-- The left class becomes the literal trivial-cofibration class after
evaluating an outer reversal-simplex object and taking opposites. -/
private theorem evaluationOpposite_leftClass (m : ReverseSimplex)
    {X Y : OppositeOuterDiagram} (f : X ⟶ Y) (hf : leftClass f) :
    trivialCofibrations Coefficientᵒᵖ ((evaluationOpposite m).map f) := by
  rw [trivialCofibrations_op]
  change (trivialFibrations Coefficient) (f.unop.app m)
  change outerTrivialFibrations f.unop at hf
  rw [outerTrivialFibrations_eq] at hf
  exact hf m

/-- Every evaluated relative matching map is an actual fibration. -/
theorem evaluated_terminalProjection_relativeMatching
    (m : ReverseSimplex) (n : ℕ) :
    fibrations Coefficientᵒᵖ
      (relativeMatchingMap n
        (Functor.whiskerRight terminalProjectionOpposite (evaluationOpposite m))) := by
  exact (ReedyCoefficientChange.relativeMatchingMap_property_iff
    (fibrations Coefficientᵒᵖ) (evaluationOpposite m) n terminalProjectionOpposite).mp
      (evaluationOpposite_rightClass m _
        (terminalProjectionOpposite_relativeMatching n))

/-- Every evaluated relative latching map is an actual trivial
cofibration in the opposite model category. -/
theorem evaluated_comparison_relativeLatching
    (m : ReverseSimplex) (n : ℕ) :
    trivialCofibrations Coefficientᵒᵖ
      (relativeLatchingMap n
        (Functor.whiskerRight comparisonOpposite (evaluationOpposite m))) := by
  exact (ReedyCoefficientChange.relativeLatchingMap_property_iff
    (trivialCofibrations Coefficientᵒᵖ) (evaluationOpposite m) n comparisonOpposite).mp
      (evaluationOpposite_leftClass m _ (comparisonOpposite_relativeLatching n))

/-- At each reversal-simplex index the constructed opposite frame is
fibrant for the actual Reedy model structure. -/
theorem evaluatedGammaOpposite_isFibrant (m : ReverseSimplex) :
    IsFibrant (GammaOpposite ⋙ evaluationOpposite m) := by
  let T := (⊤_ (SimplexCategoryᵒᵖ ⥤ OppositeOuterDiagram)) ⋙
    evaluationOpposite m
  let p : GammaOpposite ⋙ evaluationOpposite m ⟶ T :=
    Functor.whiskerRight terminalProjectionOpposite (evaluationOpposite m)
  have hT : IsTerminal T :=
    terminalIsTerminal.isTerminalObj
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ OppositeOuterDiagram Coefficientᵒᵖ).obj
        (evaluationOpposite m)) _
  apply (isFibrant_iff_of_isTerminal p hT).mpr
  apply (fibration_iff p).mpr
  exact evaluated_terminalProjection_relativeMatching m

/-- The same assertion with the outer variable first. -/
theorem GammaOuter_op_isFibrant (m : ReverseSimplex) :
    IsFibrant (GammaOuter.obj m).op := by
  change IsFibrant (GammaOpposite ⋙ evaluationOpposite m)
  exact evaluatedGammaOpposite_isFibrant m

/-- The evaluated comparison is levelwise a weak equivalence in the
opposite actual Bergner model. -/
theorem evaluatedComparison_weak (m : ReverseSimplex) :
    simplicialReedyWeakEquivalences Coefficientᵒᵖ
      (Functor.whiskerRight comparisonOpposite (evaluationOpposite m)) := by
  have htriv : reedyLatchingProperty (trivialCofibrations Coefficientᵒᵖ)
      (Functor.whiskerRight comparisonOpposite (evaluationOpposite m)) :=
    evaluated_comparison_relativeLatching m
  rw [← simplicialReedyCofibrations_inf_weakEquivalences Coefficientᵒᵖ] at htriv
  exact htriv.2

/-- Each component of the actual frame comparison is a weak equivalence
in the original dagger simplicial-category model. -/
theorem comparison_component_weak (m : ReverseSimplex) (n : ℕ) :
    weakEquivalences Coefficient ((comparison.app ⦋n⦌).app m) := by
  have hw := evaluatedComparison_weak m (op ⦋n⦌)
  rw [weakEquivalences_op] at hw
  change weakEquivalences Coefficient
    ((comparisonOpposite.app (op ⦋n⦌)).unop.app m) at hw
  exact hw

/-- The componentwise equivalence is the literal DK weak-equivalence
class of the actual global model. -/
theorem comparison_component_daggerDK (m : ReverseSimplex) (n : ℕ) :
    DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement
      ((comparison.app ⦋n⦌).app m) := by
  rw [← DaggerActualRigidificationQuillen.target_weak]
  exact comparison_component_weak m n

end

end DaggerModels.PartII.JTRelativeReedyFrame
