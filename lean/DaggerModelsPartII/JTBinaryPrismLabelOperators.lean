import DaggerModelsPartII.JTBinaryPrismRealization
import DaggerModelsPartII.JTPaddedTimeOperators
import DaggerModelsPartII.JTParameterBlockOperators
import DaggerModelsPartII.JTHigherInterleavedOperators

/-! Reindexing the full glued labels along the two endpoint-preserving operators. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBinaryPrismLabelOperators

open JTOrderedLabelBinaryGlue
open JTBinaryPrismRealization (blockInputs)
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTParameterBlocks
open JTParameterBlockOperators (leftRet_map rightRet_map)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev L (W : Source) (x y : Vertex W) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode}
variable {k l k' l' : SimplexCategory}
variable (a : (L W x z T).obj (op k')) (b : (L W z y U).obj (op l'))
variable (f : k ⟶ k') (g : l ⟶ l')
variable (hf : f.toOrderHom (Fin.last k.len) = Fin.last k'.len) (hg : g.toOrderHom 0 = 0)

private abbrev block := JTParameterBlockOperators.map f g

include hf hg in
private theorem blockInputs_map :
    reindex (block f g) (blockInputs a b) =
      blockInputs ((L W x z T).map f.op a) ((L W z y U).map g.op b) := by
  have hl : (L W x z T).map (block f g).op ((L W x z T).map (leftRet k' l').op a) =
      (L W x z T).map (leftRet k l).op ((L W x z T).map f.op a) := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, leftRet_map f g hf]
  have hr : (L W z y U).map (block f g).op ((L W z y U).map (rightRet k' l').op b) =
      (L W z y U).map (rightRet k l).op ((L W z y U).map g.op b) := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, rightRet_map f g hg]
  exact congrArg₂ (Inputs.mk (W := W) (T := T) (U := U) (k := common k l)
    (x := x) (z := z) (y := y)) hl hr

include hf hg in
/-- Both block retractions and the connector agree on the original full label. -/
theorem label_map :
    (L W x y (code T U)).map (block f g).op (orderedTriplePoint (blockInputs a b)) =
      orderedTriplePoint
        (blockInputs ((L W x z T).map f.op a) ((L W z y U).map g.op b)) := by
  rw [orderedTriplePoint_map, blockInputs_map a b f g hf hg]

open JTHigherInterleavedParameter (vertexEquiv vertexEquiv_val mapTime mapTime_vertexEquiv)
open JTPaddedTimeOperators (pad)

private theorem interleaved_first (k n : SimplexCategory) :
    vertexEquiv k n (0, 0) = 0 := by
  apply Fin.ext
  rw [vertexEquiv_val]
  simp

private theorem interleaved_last (k n : SimplexCategory) :
    vertexEquiv k n (Fin.last k.len, Fin.last n.len) =
      Fin.last (JTHigherInterleavedParameter.common k n).len := by
  apply Fin.ext
  rw [vertexEquiv_val]
  change n.len + (n.len + 1) * k.len = k.len * (n.len + 1) + n.len
  rw [Nat.mul_comm (n.len + 1), Nat.add_comm]

/-- Padding makes the entire interleaved operator preserve its first vertex. -/
theorem padded_first (k : SimplexCategory) {m n : SimplexCategory} (u : m ⟶ n) :
    (mapTime k (JTPaddedTimeOperators.map u)).toOrderHom 0 = 0 := by
  have h := mapTime_vertexEquiv k (JTPaddedTimeOperators.map u) (0, 0)
  rwa [JTPaddedTimeOperators.map_first, interleaved_first, interleaved_first] at h

/-- Padding makes the entire interleaved operator preserve its last vertex. -/
theorem padded_last (k : SimplexCategory) {m n : SimplexCategory} (u : m ⟶ n) :
    (mapTime k (JTPaddedTimeOperators.map u)).toOrderHom
        (Fin.last (JTHigherInterleavedParameter.common k (pad m)).len) =
      Fin.last (JTHigherInterleavedParameter.common k (pad n)).len := by
  have h := mapTime_vertexEquiv k (JTPaddedTimeOperators.map u)
    (Fin.last k.len, Fin.last (pad m).len)
  rwa [JTPaddedTimeOperators.map_last, interleaved_last, interleaved_last] at h

end

end DaggerModels.PartII.JTBinaryPrismLabelOperators
