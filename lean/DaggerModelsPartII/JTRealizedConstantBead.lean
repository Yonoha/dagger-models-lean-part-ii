import DaggerModelsPartII.JTIdentityRowRealization
import DaggerModelsPartII.JTParameterVertexKan

/-!
# A realized horizontal identity bead is constant at every parameter vertex

The face hypothesis is an equality of the complete native label coefficient.
The conclusion is an equality of entire simplicial-set maps, at the unchanged
original raw zero-generator vertex, for arbitrary inner degree `k`.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerModels.PartII.JTProjectiveOrderedFiberComparison
open DaggerModels.PartII.JTNecklaceLabelRealization
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTRealizedConstantBead

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev E : SSet.{0} := (single 1).toSSet
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k

private def vertexArrow (k : SimplexCategory) (a : Fin (k.len + 1)) :
    ⦋0⦌ ⟶ k := SimplexCategory.const ⦋0⦌ k a

private def outerStart : E ⟶ E ⊗ J ⦋0⦌ :=
  CartesianMonoidalCategory.lift (𝟙 E)
    (SSet.stdSimplex.isTerminalObj₀.from E ≫
      JTCylinderCEComparison.simplexUnit.app ⦋0⦌)

/-- The selected actual parameter vertex is the image of the zero-simplex
free-groupoid unit under the same inner simplex operator. -/
private theorem vertex_eq_unit (k : SimplexCategory) (a : Fin (k.len + 1)) :
    JTParameterContraction.parameterVertex k a =
      JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
        GroupoidSimplex.parameter.map (vertexArrow k a) := by
  calc
    _ = SSet.stdSimplex.map (vertexArrow k a) ≫
          JTCylinderCEComparison.simplexUnit.app k :=
      (JTParameterVertexKan.simplexUnit_vertex k a).symm
    _ = _ := JTCylinderCEComparison.simplexUnit.naturality (vertexArrow k a)

/-- A native bead at the selected actual parameter vertex factors through
the degree-zero starting bead and the full parameter naturality map. -/
private theorem lift_vertex_factor (k : SimplexCategory)
    (a : Fin (k.len + 1)) (X : SSet.{0}) (b : E ⟶ X) :
    CartesianMonoidalCategory.lift b
        (SSet.stdSimplex.isTerminalObj₀.from E ≫
          JTParameterContraction.parameterVertex k a) =
      outerStart ≫
        (b ⊗ₘ GroupoidSimplex.parameter.map (vertexArrow k a)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [outerStart, Category.assoc, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.lift_fst_assoc,
      Category.id_comp]
  · simp only [outerStart, Category.assoc, CartesianMonoidalCategory.lift_snd,
      CartesianMonoidalCategory.tensorHom_snd, CartesianMonoidalCategory.lift_snd_assoc,
      vertex_eq_unit]

/-- A horizontal bead whose selected face is the actual identity-row edge
realizes to the unchanged raw vertex on the entire native one-edge source. -/
theorem realized_constant_bead (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory) (a : Fin (k.len + 1))
    (X : SSet.{0}) (b : E ⟶ X)
    (η : (diagramMappingSpace (F.obj X) W).obj (op k))
    (hface : (diagramTensor (F.obj E)).map
        (SSet.stdSimplex.map (vertexArrow k a)) ≫
      (Functor.whiskerRight (F.map b)
        (tensorRight (SSet.stdSimplex.obj k)) ≫ η) =
          JTIdentityRowRealization.identityEdgeLabel W x) :
    CartesianMonoidalCategory.lift b
        (SSet.stdSimplex.isTerminalObj₀.from E ≫
          JTParameterContraction.parameterVertex k a) ≫
      realizedLabel X W k η =
        SSet.stdSimplex.isTerminalObj₀.from E ≫
          SSet.yonedaEquiv.symm
            (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) := by
  let q : (Δ[0] : SSet.{0}) ⟶
      OrdinaryJTRealization.realization.obj
        (JTReversalInput.ordinaryInput.obj W) :=
    SSet.yonedaEquiv.symm
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
  calc
    _ = outerStart ≫
          (b ⊗ₘ GroupoidSimplex.parameter.map (vertexArrow k a)) ≫
            realizedLabel X W k η := by
      rw [lift_vertex_factor, Category.assoc]
    _ = outerStart ≫
          (𝟙 E ⊗ₘ GroupoidSimplex.parameter.map (vertexArrow k a)) ≫
          (b ⊗ₘ 𝟙 (J k)) ≫ realizedLabel X W k η := by
      rw [← Category.assoc
        (𝟙 E ⊗ₘ GroupoidSimplex.parameter.map (vertexArrow k a))
        (b ⊗ₘ 𝟙 (J k)), tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    _ = outerStart ≫
          (𝟙 E ⊗ₘ GroupoidSimplex.parameter.map (vertexArrow k a)) ≫
          realizedLabel E W k
            (Functor.whiskerRight (F.map b)
              (tensorRight (SSet.stdSimplex.obj k)) ≫ η) := by
      rw [realizedLabel_natural_X]
    _ = outerStart ≫ realizedLabel E W ⦋0⦌
          ((diagramTensor (F.obj E)).map
              (SSet.stdSimplex.map (vertexArrow k a)) ≫
            (Functor.whiskerRight (F.map b)
              (tensorRight (SSet.stdSimplex.obj k)) ≫ η)) := by
      rw [realizedLabel_natural_k]
    _ = outerStart ≫ realizedLabel E W ⦋0⦌
          (JTIdentityRowRealization.identityEdgeLabel W x) := by
      rw [hface]
    _ = SSet.stdSimplex.isTerminalObj₀.from E ≫ q := by
      rw [JTIdentityRowRealization.realizedIdentityEdgeLabel]
      have h : outerStart ≫
          SSet.stdSimplex.isTerminalObj₀.from (E ⊗ J ⦋0⦌) =
            SSet.stdSimplex.isTerminalObj₀.from E :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [← Category.assoc, h]
    _ = _ := rfl

end

end DaggerModels.PartII.JTRealizedConstantBead
