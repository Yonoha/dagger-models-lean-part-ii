import DaggerModelsPartII.JTJointTraceObstruction
import DaggerModelsPartII.JTCodiscreteParameterPairing
import DaggerModelsPartII.JTParameterVertexKan

/-! A one-bead constant-label family with a horizontally varying parameter. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointTraceActualCounterexample

open JTJointTraceObstruction
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev T := NecklaceCode.single 1
private abbrev A := Discrete PUnit

variable (W : Source) (z : Vertex W)

private def natives : A ⥤ NecklaceCode := (Functor.const A).obj T
private def degrees : A ⥤ SimplexCategory := (Functor.const A).obj ⦋1⦌
private def times : A ⥤ SimplexCategory := (Functor.const A).obj ⦋0⦌
private def labels := JTConstantOrderedLabelDiagram.diagram W z (natives) degrees
private def target : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W z) :=
  NecklacesOver.point (rawVertex W z)

private def parameter : T.toSSet ⊗ J.obj ⦋0⦌ ⟶ J.obj ⦋1⦌ :=
  fst T.toSSet (J.obj ⦋0⦌) ≫ (NecklaceCode.singleIso 1).hom ≫
    JTCylinderCEComparison.simplexUnit.app ⦋1⦌

/-- The actual constant-label family obeys the full original raw equation. -/
def family : JTParametrizedTargetFamilies.Family (target W z) (labels W z) times where
  collapse := {
    app := fun _ ↦ JTOrderedLabelJointInsertion.toPoint T
    naturality := by
      intro a b f
      have hab : a = b := Subsingleton.elim _ _
      subst b
      have hf : f = 𝟙 a := Subsingleton.elim _ _
      subst f
      simp }
  parameter := fun _ ↦ parameter
  parameter_map := by
    intro a b f
    have hab : a = b := Subsingleton.elim _ _
    subst b
    have hf : f = 𝟙 a := Subsingleton.elim _ _
    subst f
    change (𝟙 T.toSSet ⊗ₘ 𝟙 (J.obj ⦋0⦌)) ≫ parameter = parameter
    simp
  raw := by
    intro a
    exact constant_raw_overPoint W z T ⦋1⦌ ⦋0⦌ (parameter)

private theorem first_standard :
    SSet.yonedaEquiv.symm T.first ≫ (NecklaceCode.singleIso 1).hom =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  apply SSet.stdSimplex.obj₀Equiv.injective
  simpa only [SSet.stdSimplex.obj₀Equiv_apply] using
    (NecklaceCode.singleIso_vertex.{0} 1 T.first)

private theorem last_standard :
    SSet.yonedaEquiv.symm T.last ≫ (NecklaceCode.singleIso 1).hom =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  apply SSet.stdSimplex.obj₀Equiv.injective
  simpa only [SSet.stdSimplex.obj₀Equiv_apply] using
    (NecklaceCode.singleIso_vertex.{0} 1 T.last)

private def firstTensor : (Δ[0] : SSet.{0}) ⊗ J.obj ⦋0⦌ ⟶ T.toSSet ⊗ J.obj ⦋0⦌ :=
  SSet.yonedaEquiv.symm T.first ⊗ₘ 𝟙 (J.obj ⦋0⦌)

private def lastTensor : (Δ[0] : SSet.{0}) ⊗ J.obj ⦋0⦌ ⟶ T.toSSet ⊗ J.obj ⦋0⦌ :=
  SSet.yonedaEquiv.symm T.last ⊗ₘ 𝟙 (J.obj ⦋0⦌)

private theorem parameter_first :
    firstTensor ≫ parameter = fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫
      JTParameterContraction.parameterVertex ⦋1⦌ 0 := by
  calc
    firstTensor ≫ parameter =
        fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫
          SSet.yonedaEquiv.symm T.first ≫ (NecklaceCode.singleIso 1).hom ≫
            JTCylinderCEComparison.simplexUnit.app ⦋1⦌ := by
      simp only [firstTensor, parameter, ← Category.assoc, tensorHom_fst]
    _ = _ := by
      have hc : SSet.yonedaEquiv.symm T.first ≫ (NecklaceCode.singleIso 1).hom ≫
          JTCylinderCEComparison.simplexUnit.app ⦋1⦌ =
          JTParameterContraction.parameterVertex ⦋1⦌ 0 := by
        rw [← Category.assoc, first_standard, JTParameterVertexKan.simplexUnit_vertex]
      exact congrArg (fun q ↦ fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫ q) hc

private theorem parameter_last :
    lastTensor ≫ parameter = fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫
      JTParameterContraction.parameterVertex ⦋1⦌ 1 := by
  calc
    lastTensor ≫ parameter =
        fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫
          SSet.yonedaEquiv.symm T.last ≫ (NecklaceCode.singleIso 1).hom ≫
            JTCylinderCEComparison.simplexUnit.app ⦋1⦌ := by
      simp only [lastTensor, parameter, ← Category.assoc, tensorHom_fst]
    _ = _ := by
      have hc : SSet.yonedaEquiv.symm T.last ≫ (NecklaceCode.singleIso 1).hom ≫
          JTCylinderCEComparison.simplexUnit.app ⦋1⦌ =
          JTParameterContraction.parameterVertex ⦋1⦌ 1 := by
        rw [← Category.assoc, last_standard, JTParameterVertexKan.simplexUnit_vertex]
      exact congrArg (fun q ↦ fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫ q) hc

/-- The actual constant-label Family parameter varies horizontally at one time. -/
theorem parameter_not_time_only :
    ¬ ∃ trace : J.obj ⦋0⦌ ⟶ J.obj ⦋1⦌,
      parameter = snd T.toSSet (J.obj ⦋0⦌) ≫ trace := by
  rintro ⟨trace, h⟩
  have heq : JTParameterContraction.parameterVertex ⦋1⦌ 0 =
      JTParameterContraction.parameterVertex ⦋1⦌ 1 := by
    let σ := lift (𝟙 (Δ[0] : SSet.{0}))
      (JTParameterContraction.parameterVertex ⦋0⦌ 0)
    have hs : σ ≫ fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) =
        𝟙 (Δ[0] : SSet.{0}) := by
      dsimp only [σ]
      exact lift_fst _ _
    have hf : firstTensor ≫ snd T.toSSet (J.obj ⦋0⦌) =
        snd (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) := tensorHom_snd _ _
    have hl : lastTensor ≫ snd T.toSSet (J.obj ⦋0⦌) =
        snd (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) := tensorHom_snd _ _
    have hh : fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫
        JTParameterContraction.parameterVertex ⦋1⦌ 0 =
      fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫
        JTParameterContraction.parameterVertex ⦋1⦌ 1 := by
      calc
        _ = firstTensor ≫ parameter := parameter_first.symm
        _ = firstTensor ≫ snd T.toSSet (J.obj ⦋0⦌) ≫ trace := by rw [h]
        _ = snd (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫ trace := by rw [← Category.assoc, hf]
        _ = lastTensor ≫ snd T.toSSet (J.obj ⦋0⦌) ≫ trace := by rw [← Category.assoc, hl]
        _ = lastTensor ≫ parameter := by rw [h]
        _ = _ := parameter_last
    have hh' := congrArg (fun f ↦ σ ≫ f) hh
    simpa only [← Category.assoc, hs, Category.id_comp] using hh'
  have hv := congrArg (fun f : (Δ[0] : SSet.{0}) ⟶ J.obj ⦋1⦌ ↦
    JTCodiscreteParameterPairing.coord ⦋1⦌ (op ⦋0⦌)
      (f.app (op ⦋0⦌) (NecklaceCode.zeroSimplex 0)) 0) heq
  dsimp only at hv
  rw [JTCodiscreteParameterPairing.coord_vertex,
    JTCodiscreteParameterPairing.coord_vertex] at hv
  exact (by decide : (0 : Fin 2) ≠ 1) hv

/-- The failure occurs in the parameter field of the actual full-raw Family. -/
theorem family_parameter_not_time_only :
    ¬ ∃ trace : J.obj ⦋0⦌ ⟶ J.obj ⦋1⦌,
      (family W z).parameter (Discrete.mk PUnit.unit) =
        snd T.toSSet (J.obj ⦋0⦌) ≫ trace :=
  parameter_not_time_only

end

end DaggerModels.PartII.JTJointTraceActualCounterexample
