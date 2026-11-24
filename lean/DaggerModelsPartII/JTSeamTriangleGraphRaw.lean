import DaggerModelsPartII.JTWhiskeredGraphRaw
import DaggerModelsPartII.JTRelativeSeamTriangle

/-! The actual stationary seam triangle has the original joint raw value on supported graphs. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSeamTriangleGraphRaw

open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTNativeRowLabel (labelFromRow)
open ReversalDiscreteFreeColimits (discreteFree)
open TwoBeadEndpointLabel (jointLabelFromRow jointLabelFromRow_vertex)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev free := discreteFree.{0}

variable (W : Source) (z : Vertex W)

/-- The native coefficient of the literal identity triangle is the full
constant coefficient, at the same original coefficient degree. -/
theorem identityTriangle_coefficient (k : SimplexCategory) :
    (term (std.obj k) ≫ vertexPoint W z ≫ JTRelativeSeamTriangle.identityTriangle W) ≫
      labelFromRow W 2 = JTConstantOrderedLabel.constantCoefficient W z (single 2) k := by
  let r := SimplexCategory.const ⦋2⦌ ⦋0⦌ 0
  let h₀ : r.toOrderHom 0 = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
  let h₁ : r.toOrderHom (Fin.last 2) = Fin.last 0 :=
    @Subsingleton.elim (Fin 1) inferInstance _ _
  let c := JTMixedGraphHorizontalTraversal.singleOperator r h₀ h₁
  have h := JTMixedGraphHorizontalLabel.labelFromRow_natural W r h₀ h₁
  change labelFromRow W 0 ≫ diagramMappingPrecomp (free.map c.map) W =
    JTRelativeSeamTriangle.identityTriangle W ≫ labelFromRow W 2 at h
  have ht : c.map ≫ (singleIso 0).hom = term (single 2).toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hc : JTRelativeSeamTriangle.identityTriangle W ≫ labelFromRow W 2 =
      jointLabelFromRow W ≫ diagramMappingPrecomp (free.map (term (single 2).toSSet)) W := by
    rw [← h]
    simp only [labelFromRow, jointLabelFromRow, Category.assoc,
      ← diagramMappingPrecomp_comp, ← free.map_comp, ht]
  simp only [Category.assoc]
  rw [hc, ← Category.assoc (vertexPoint W z), jointLabelFromRow_vertex]
  rfl

/-- A stationary face of the full triangle coefficient is the literal
constant native coefficient on that WHOLE face. -/
theorem coefficient_onFace {s k : SimplexCategory} (u : s ⟶ k)
    (τ : std.obj k ⟶ row W ⦋2⦌)
    (hτ : std.map u ≫ τ =
      term (std.obj s) ≫ vertexPoint W z ≫ JTRelativeSeamTriangle.identityTriangle W) :
    std.map u ≫ (τ ≫ labelFromRow W 2) =
      JTConstantOrderedLabel.constantCoefficient W z (single 2) s := by
  rw [← Category.assoc, hτ, identityTriangle_coefficient]

/-- A supported parameter gives the exact original joint raw value on any
graph domain. The triangle may vary away from its prescribed stationary face. -/
theorem graph_raw {X : SSet.{0}} {s k : SimplexCategory} (u : s ⟶ k)
    (τ : std.obj k ⟶ row W ⦋2⦌)
    (hτ : std.map u ≫ τ =
      term (std.obj s) ≫ vertexPoint W z ≫ JTRelativeSeamTriangle.identityTriangle W)
    (h : X ⟶ (single 2).toSSet) (q : X ⟶ J.obj s) :
    lift h (q ≫ J.map u) ≫ realizedLabel (single 2).toSSet W k
      (SSet.yonedaEquiv (τ ≫ labelFromRow W 2)) =
      h ≫ term (single 2).toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  rw [JTWhiskerEdgeGraphRaw.coefficient_reindex, coefficient_onFace W z u τ hτ]
  have hr := JTComposedPrismLabels.rawProduct_constant W z (single 2)
    (snd (single 2).toSSet (J.obj s))
  dsimp only [JTComposedPrismLabels.rawProduct, JTBinaryPrismRealization.realizeProduct] at hr
  rw [lift_fst_snd, Category.id_comp] at hr
  rw [hr, lift_fst_assoc]

end

end DaggerModels.PartII.JTSeamTriangleGraphRaw
