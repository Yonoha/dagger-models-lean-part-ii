import DaggerModelsPartII.JTEndpointNormalizationLifts
import DaggerModelsPartII.TwoBeadEndpointLabel
import DaggerModelsPartII.JTRealizedLabelEndpoints

/-!
# The actual identity row realizes as the unchanged raw vertex

The complete original row-zero degeneracy is transported through the same
free-simplex mapping isomorphisms used by the two-bead endpoint labels.
Its degree-zero label is the original zero label precomposed by the native
single-edge terminal map. Realization is therefore the entire constant
simplicial-set map at the original raw zero-generator vertex.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerModels.PartII.JTProjectiveOrderedFiberComparison
open DaggerModels.PartII.OrderedNecklaceVertexPoints
open DaggerModels.PartII.JTNecklaceLabelRealization
open DaggerModels.PartII.JTRealizedLabelEndpoints
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTIdentityRowRealization

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev E : SSet.{0} := (single 1).toSSet
private abbrev collapse : ⦋1⦌ ⟶ ⦋0⦌ :=
  SimplexCategory.const ⦋1⦌ ⦋0⦌ 0

variable (W : Source)

/-- The original row restriction identities are natural also along the
horizontal degeneracy, with no endpoint or fibrancy premise. -/
private theorem rowRestriction_collapse :
    (rowRestrictionIso W ⦋0⦌).inv ≫
        (JTRealizationDiagonal.ordinaryCurry.obj
          (JTReversalInput.ordinaryInput.obj W)).map collapse.op =
      W.map (ReverseSimplex.inclusion.map collapse).op ≫
        (rowRestrictionIso W ⦋1⦌).inv := by
  apply NatTrans.ext
  funext q z
  dsimp [rowRestrictionIso, row, JTRealizationDiagonal.ordinaryCurry,
    JTReversalInput.ordinaryInput]
  simp

/-- The original free-simplex/row comparison respects the actual collapse
of the standard one-simplex to the standard zero-simplex. -/
private theorem freeSimplexRowIso_collapse :
    diagramMappingPrecomp
        (SegalRepresentables.freeSimplices.map collapse) W ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom =
    (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom ≫
      JTEndpointNormalizationLifts.identityFamily W := by
  have hn := OrderedSimplexEndpointFiber.freeSimplexMappingIso_natural W collapse
  change diagramMappingPrecomp
      (SegalRepresentables.freeSimplices.map collapse) W ≫
        (OrderedSimplexEndpointFiber.freeMappingIso W 1).hom =
      (OrderedSimplexEndpointFiber.freeMappingIso W 0).hom ≫
        W.map (ReverseSimplex.inclusion.map collapse).op at hn
  have hr := rowRestriction_collapse W
  calc
    _ = (diagramMappingPrecomp
          (SegalRepresentables.freeSimplices.map collapse) W ≫
            (OrderedSimplexEndpointFiber.freeMappingIso W 1).hom) ≫
          (rowRestrictionIso W ⦋1⦌).inv := by
            simp only [OrderedSimplexEndpointFiber.freeSimplexRowIso,
              Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = ((OrderedSimplexEndpointFiber.freeMappingIso W 0).hom ≫
          W.map (ReverseSimplex.inclusion.map collapse).op) ≫
          (rowRestrictionIso W ⦋1⦌).inv := by rw [hn]
    _ = (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom ≫
          JTEndpointNormalizationLifts.identityFamily W := by
            rw [Category.assoc, ← hr]
            simp only [OrderedSimplexEndpointFiber.freeSimplexRowIso,
              Iso.trans_hom, Iso.symm_hom, JTEndpointNormalizationLifts.identityFamily,
              Category.assoc]

/-- The native single-edge terminal map is exactly the standard-simplex
collapse after the retained single-bead isomorphism. -/
private theorem nativeTerminal :
    F.map (singleIso 1).hom ≫
      SegalRepresentables.freeSimplices.map collapse =
        F.map (SSet.stdSimplex.isTerminalObj₀.from E) := by
  have h : (singleIso.{0} 1).hom ≫ SSet.stdSimplex.map collapse =
      SSet.stdSimplex.isTerminalObj₀.from E :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  change F.map (singleIso 1).hom ≫ F.map (SSet.stdSimplex.map collapse) = _
  rw [← F.map_comp, h]

/-- The original complete row-zero identity family gives the strict
single-edge label induced from the SAME zero-row label. -/
theorem identityFamily_edgeLabel :
    JTEndpointNormalizationLifts.identityFamily W ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W =
      TwoBeadEndpointLabel.jointLabelFromRow W ≫
        diagramMappingPrecomp
          (F.map (SSet.stdSimplex.isTerminalObj₀.from E)) W := by
  have h := freeSimplexRowIso_collapse W
  have h' : JTEndpointNormalizationLifts.identityFamily W ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).inv =
        (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv ≫
          diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map collapse) W := by
    calc
      _ = (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv ≫
            ((OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom ≫
              JTEndpointNormalizationLifts.identityFamily W) ≫
            (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).inv := by
              simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := by
        rw [← h]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = (JTEndpointNormalizationLifts.identityFamily W ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).inv) ≫
          diagramMappingPrecomp (F.map (singleIso 1).hom) W := by
            rfl
    _ = (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv ≫
          (diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map collapse) W ≫
            diagramMappingPrecomp (F.map (singleIso 1).hom) W) := by
              rw [h', Category.assoc]
    _ = _ := by
      rw [← diagramMappingPrecomp_comp, nativeTerminal]
      rfl

variable (x : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- The literal degree-zero label of the original horizontal identity row. -/
def identityEdgeLabel :
    (diagramMappingSpace (F.obj E) W).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv
    (vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W ≫
      TwoBeadEndpointLabel.edgeLabelFromRow W)

/-- This is the actual zero label precomposed by the native terminal map,
including the complete original natural transformation. -/
theorem identityEdgeLabel_eq_zeroLabel :
    identityEdgeLabel W x =
      Functor.whiskerRight
        (F.map (SSet.stdSimplex.isTerminalObj₀.from E))
        (tensorRight (Δ[0] : SSet.{0})) ≫ zeroLabel W x := by
  have h := congrArg SSet.yonedaEquiv
    (show vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W =
      zeroPoint W x ≫ diagramMappingPrecomp
        (F.map (SSet.stdSimplex.isTerminalObj₀.from E)) W by
      rw [identityFamily_edgeLabel, ← Category.assoc,
        TwoBeadEndpointLabel.jointLabelFromRow_vertex])
  simpa only [identityEdgeLabel, SSet.yonedaEquiv_comp, zeroPoint,
    Equiv.apply_symm_apply, diagramMappingPrecomp] using h

/-- The entire realized identity-edge label is constant at the unchanged
raw zero-generator vertex; this is an equality of full simplicial-set maps. -/
theorem realizedIdentityEdgeLabel :
    realizedLabel E W ⦋0⦌ (identityEdgeLabel W x) =
      SSet.stdSimplex.isTerminalObj₀.from
          (E ⊗ GroupoidSimplex.parameter.obj ⦋0⦌) ≫
        SSet.yonedaEquiv.symm
          (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) := by
  rw [identityEdgeLabel_eq_zeroLabel]
  rw [← realizedLabel_natural_X
    (SSet.stdSimplex.isTerminalObj₀.from E) W ⦋0⦌ (zeroLabel W x)]
  rw [JTRealizedLabelEndpoints.realizedZeroLabel]
  change ((SSet.stdSimplex.isTerminalObj₀.from E ⊗ₘ
      𝟙 (GroupoidSimplex.parameter.obj ⦋0⦌)) ≫
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌)) ≫
      SSet.yonedaEquiv.symm
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) = _
  have ht : (SSet.stdSimplex.isTerminalObj₀.from E ⊗ₘ
      𝟙 (GroupoidSimplex.parameter.obj ⦋0⦌)) ≫
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌) =
      SSet.stdSimplex.isTerminalObj₀.from
        (E ⊗ GroupoidSimplex.parameter.obj ⦋0⦌) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht]

end

end DaggerModels.PartII.JTIdentityRowRealization
