import DaggerModelsPartII.JTNativeRowCoefficientOperators
import DaggerModelsPartII.JTWhiskerEdgeGraphRaw

/-! Horizontally degenerate coefficients on native single beads of any degree. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTStationarySimplexCoefficient

open JTProjectiveOrderedFiberComparison (row vertexPoint)
open ReversalDiscreteFreeColimits (discreteFree)
open JTNativeRowLabel (labelFromRow)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)

variable (W : Source) (z : Vertex W) (d : ℕ) (k : SimplexCategory)

/-- The entire horizontal `d`-simplex is the degeneracy of one original vertex. -/
def degenerateRow : std.obj k ⟶ row W ⦋d⦌ :=
  term (std.obj k) ≫ vertexPoint W z ≫
    (Rows W).map (SimplexCategory.isTerminalZero.from ⦋d⦌).op

/-- The native label of an arbitrary degenerate horizontal simplex is the
literal constant coefficient on the single bead of the same degree. -/
theorem degenerateRow_label :
    degenerateRow W z d k ≫ labelFromRow W d =
      JTConstantOrderedLabel.constantCoefficient W z (single d) k := by
  let r := SimplexCategory.isTerminalZero.from ⦋d⦌
  have h := JTNativeRowCoefficientOperators.labelFromRow_operator W r
  have ht : JTNativeRowCoefficientOperators.nativeOperator r ≫ (singleIso 0).hom =
      term (single d).toSSet := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have h' : (Rows W).map r.op ≫ labelFromRow W d =
      TwoBeadEndpointLabel.jointLabelFromRow W ≫
        diagramMappingPrecomp (discreteFree.map (term (single d).toSSet)) W := by
    rw [← h]
    simp only [labelFromRow, TwoBeadEndpointLabel.jointLabelFromRow,
      Category.assoc, ← diagramMappingPrecomp_comp, ← discreteFree.map_comp]
    rw [ht]
  simp only [degenerateRow, Category.assoc]
  rw [h', ← Category.assoc (vertexPoint W z),
    TwoBeadEndpointLabel.jointLabelFromRow_vertex]
  rfl

variable {l : SimplexCategory} (u : l ⟶ k)
variable (τ : std.obj k ⟶ row W ⦋d⦌)

/-- A row simplex stationary on an ordinal face has the constant native
single-bead coefficient on that entire face. -/
theorem coefficient_onFace
    (hτ : std.map u ≫ τ = degenerateRow W z d l) :
    std.map u ≫ (τ ≫ labelFromRow W d) =
      JTConstantOrderedLabel.constantCoefficient W z (single d) l := by
  rw [← Category.assoc, hτ, degenerateRow_label]

variable {X : SSet.{0}} (h : X ⟶ (single d).toSSet) (θ : X ⟶ J.obj l)

/-- A graph with parameter in the stationary face has the joint raw value,
for any horizontal single-bead dimension. -/
theorem raw_onFace
    (hτ : std.map u ≫ τ = degenerateRow W z d l) :
    lift h (θ ≫ J.map u) ≫ realizedLabel (single d).toSSet W k
        (SSet.yonedaEquiv (τ ≫ labelFromRow W d)) =
      h ≫ term (single d).toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  rw [JTWhiskerEdgeGraphRaw.coefficient_reindex]
  rw [coefficient_onFace W z d k u τ hτ]
  have hr := JTComposedPrismLabels.rawProduct_constant W z (single d)
    (snd (single d).toSSet (J.obj l))
  dsimp only [JTComposedPrismLabels.rawProduct,
    JTBinaryPrismRealization.realizeProduct] at hr
  rw [lift_fst_snd, Category.id_comp] at hr
  rw [hr, lift_fst_assoc]

end
end DaggerModels.PartII.JTStationarySimplexCoefficient
