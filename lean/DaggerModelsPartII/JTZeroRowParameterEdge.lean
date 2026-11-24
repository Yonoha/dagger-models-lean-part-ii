import DaggerModelsPartII.JTParameterVertexKan
import DaggerModelsPartII.TwoBeadEndpointLabel
import DaggerModelsPartII.JTRealizedLabelEndpoints
import DaggerModelsPartII.JTNecklaceLabelRealization
import ChosenNecklacesOver
import OriginalFlagNormalizedBeads

/-!
# The specified zero-row groupoid path gives an actual raw realization edge

The input is an explicit `z : J[1] ⟶ row W 0`.
The output does not depend on choices of the two endpoint-normalizing lifts.
No arbitrary edge of the raw realization is claimed to have this form.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTZeroRowParameterEdge

open JTProjectiveOrderedFiberComparison TwoBeadEndpointLabel
open JTNecklaceLabelRealization JTRealizedLabelEndpoints
open DaggerOriginalFlagFlankification

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev F := discreteFree.{0}

private def vertex (i : Fin 2) : (Δ[0] : SSet.{0}) ⟶ (Δ[1] : SSet.{0}) :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)

private def zeroSimplex : (Δ[0] : SSet.{0}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)

/-- The specified `J[1]` path becomes one actual free-zero diagram label. -/
def zeroRowLabel (W : Source) (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌) :
    (diagramMappingSpace (F.obj (Δ[0] : SSet.{0})) W).obj (op ⦋1⦌) :=
  SSet.yonedaEquiv
    (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ z ≫ jointLabelFromRow W)

private theorem zeroRowLabel_face (W : Source)
    (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌) (i : Fin 2)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : JTParameterContraction.parameterVertex ⦋1⦌ i ≫ z = vertexPoint W x) :
    (diagramTensor (F.obj (Δ[0] : SSet.{0}))).map (vertex i) ≫
      zeroRowLabel W z = OrderedNecklaceVertexPoints.zeroLabel W x := by
  have h : vertex i ≫
      (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ z ≫ jointLabelFromRow W) =
      OrderedNecklaceVertexPoints.zeroPoint W x := by
    simp only [← Category.assoc, vertex,
      JTParameterVertexKan.simplexUnit_vertex, hx]
    exact jointLabelFromRow_vertex W x
  change (jointLabels W).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op
    (zeroRowLabel W z) = OrderedNecklaceVertexPoints.zeroLabel W x
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.stdSimplex.map_comp_yonedaEquiv_symm]
  simpa only [vertex, zeroRowLabel, OrderedNecklaceVertexPoints.zeroPoint,
    Equiv.symm_apply_apply] using h

/-- The complete original realized-label map on the groupoid parameter. -/
def zeroRowParameterMap (W : Source)
    (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌) : J.obj ⦋1⦌ ⟶ R W :=
  CartesianMonoidalCategory.lift
      (SSet.stdSimplex.isTerminalObj₀.from (J.obj ⦋1⦌)) (𝟙 _) ≫
    realizedLabel (Δ[0] : SSet.{0}) W ⦋1⦌ (zeroRowLabel W z)

/-- The specified ordinary edge, retaining the actual free-groupoid unit. -/
def rawEdge (W : Source) (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌) :
    (Δ[1] : SSet.{0}) ⟶ R W :=
  JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ zeroRowParameterMap W z

/-- The same edge on the original native one-bead necklace. -/
def nativeRawEdge (W : Source) (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌) :
    (single 1).toSSet ⟶ R W :=
  (singleIso 1).hom ≫ rawEdge W z

private theorem zeroRowParameterMap_vertex (W : Source)
    (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌) (i : Fin 2)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : JTParameterContraction.parameterVertex ⦋1⦌ i ≫ z = vertexPoint W x) :
    JTParameterContraction.parameterVertex ⦋1⦌ i ≫ zeroRowParameterMap W z =
      SSet.yonedaEquiv.symm
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) := by
  let δ : ⦋0⦌ ⟶ ⦋1⦌ := SimplexCategory.const ⦋0⦌ ⦋1⦌ i
  let u (k : SimplexCategory) : J.obj k ⟶ (Δ[0] : SSet.{0}) ⊗ J.obj k :=
    CartesianMonoidalCategory.lift
      (SSet.stdSimplex.isTerminalObj₀.from (J.obj k)) (𝟙 _)
  have hv : JTParameterContraction.parameterVertex ⦋1⦌ i =
      JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ J.map δ := by
    calc
      _ = vertex i ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌ :=
        (JTParameterVertexKan.simplexUnit_vertex ⦋1⦌ i).symm
      _ = _ := JTCylinderCEComparison.simplexUnit.naturality δ
  have hu : J.map δ ≫ u ⦋1⦌ =
      u ⦋0⦌ ≫ (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map δ) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [u, Category.assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.tensorHom_fst]
      exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    · simp only [u, Category.assoc, CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.tensorHom_snd]
      simp
  have hn := realizedLabel_natural_k (Δ[0] : SSet.{0}) W δ (zeroRowLabel W z)
  have hf := zeroRowLabel_face W z i x hx
  have hzero :
      JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ u ⦋0⦌ ≫
        JTRealizedLabelEndpoints.constantRawEndpoint W x ⦋0⦌ =
      SSet.yonedaEquiv.symm
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) := by
    have hfst : u ⦋0⦌ ≫
        CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) =
        SSet.stdSimplex.isTerminalObj₀.from (J.obj ⦋0⦌) := by
      simp only [u, CartesianMonoidalCategory.lift_fst]
    have hterminal : JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
        SSet.stdSimplex.isTerminalObj₀.from (J.obj ⦋0⦌) =
          𝟙 (Δ[0] : SSet.{0}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    change JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ u ⦋0⦌ ≫
        CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) (J.obj ⦋0⦌) ≫
          SSet.yonedaEquiv.symm
            (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) =
        SSet.yonedaEquiv.symm
          (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
    calc
      _ = (JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
            (u ⦋0⦌ ≫ CartesianMonoidalCategory.fst
              (Δ[0] : SSet.{0}) (J.obj ⦋0⦌))) ≫
                SSet.yonedaEquiv.symm
                  (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) := by
          simp only [Category.assoc]
      _ = (JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
            SSet.stdSimplex.isTerminalObj₀.from (J.obj ⦋0⦌)) ≫
              SSet.yonedaEquiv.symm
                (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) := by
          rw [hfst]
      _ = _ := by rw [hterminal, Category.id_comp]
  have hThree :
      (JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ J.map δ) ≫ u ⦋1⦌ =
      (JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ u ⦋0⦌) ≫
        (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map δ) := by
    calc
      _ = JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
            (J.map δ ≫ u ⦋1⦌) := Category.assoc _ _ _
      _ = JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
            (u ⦋0⦌ ≫ (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map δ)) := by rw [hu]
      _ = _ := (Category.assoc _ _ _).symm
  calc
    _ = (JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ J.map δ) ≫
          u ⦋1⦌ ≫ realizedLabel (Δ[0] : SSet.{0}) W ⦋1⦌
            (zeroRowLabel W z) := by rw [hv]; rfl
    _ = JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ u ⦋0⦌ ≫
          (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map δ) ≫
            realizedLabel (Δ[0] : SSet.{0}) W ⦋1⦌ (zeroRowLabel W z) := by
      exact congrArg (fun f ↦ f ≫ realizedLabel (Δ[0] : SSet.{0}) W ⦋1⦌
        (zeroRowLabel W z)) hThree
    _ = JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ u ⦋0⦌ ≫
          realizedLabel (Δ[0] : SSet.{0}) W ⦋0⦌
            (OrderedNecklaceVertexPoints.zeroLabel W x) := by
      rw [hn]
      exact congrArg (fun η ↦
        JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫ u ⦋0⦌ ≫
          realizedLabel (Δ[0] : SSet.{0}) W ⦋0⦌ η) hf
    _ = _ := by rw [JTRealizedLabelEndpoints.realizedZeroLabel]; exact hzero

/-- Both original raw endpoints of the specified ordinary edge. -/
theorem rawEdge_endpoint (W : Source)
    (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌) (i : Fin 2)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : JTParameterContraction.parameterVertex ⦋1⦌ i ≫ z = vertexPoint W x) :
    vertex i ≫ rawEdge W z =
      SSet.yonedaEquiv.symm
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) := by
  dsimp only [rawEdge]
  rw [← Category.assoc,
    show vertex i ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌ =
      JTParameterContraction.parameterVertex ⦋1⦌ i from
        JTParameterVertexKan.simplexUnit_vertex ⦋1⦌ i]
  exact zeroRowParameterMap_vertex W z i x hx

private theorem nativeRawEdge_first (W : Source)
    (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ z = vertexPoint W x) :
    (nativeRawEdge W z).app (op ⦋0⦌) (single 1).first =
      JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x := by
  have h := congrArg SSet.yonedaEquiv
    (rawEdge_endpoint W z 0 x hx)
  simpa only [nativeRawEdge, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply, singleIso_first] using h

private theorem nativeRawEdge_last (W : Source)
    (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌)
    (y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hy : JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ z = vertexPoint W y) :
    (nativeRawEdge W z).app (op ⦋0⦌) (single 1).last =
      JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y := by
  have h := congrArg SSet.yonedaEquiv
    (rawEdge_endpoint W z 1 y hy)
  simpa only [nativeRawEdge, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply, singleIso_last] using h

/-- The actual one-bead necklace over the unchanged raw realization. -/
def rawNecklaceOver (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (z : J.obj ⦋1⦌ ⟶ row W ⦋0⦌)
    (hx : JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ z = vertexPoint W x)
    (hy : JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ z = vertexPoint W y) :
    DaggerChosenRigidificationNecklace.NecklacesOver (R W)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y) where
  code := single 1
  map := nativeRawEdge W z
  first := nativeRawEdge_first W z x hx
  last := nativeRawEdge_last W z y hy

end

end DaggerModels.PartII.JTZeroRowParameterEdge
