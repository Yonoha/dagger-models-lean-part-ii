import DaggerModelsPartII.JTMixedGraphEndpointLifts
import DaggerModelsPartII.TwoBeadEndpointLabel

/-!
# Original row coefficients on the native single bead in every degree
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativeRowLabel

open ReversalDiscreteFreeColimits JTProjectiveOrderedFiberComparison
open OrderedSimplexEndpointFiber JTMixedGraphEndpointLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}

def labelFromRow (W : Source) (d : ℕ) :
    row W ⦋d⦌ ⟶ diagramMappingSpace (F.obj (single d).toSSet) W :=
  (freeSimplexRowIso W d).inv ≫
    diagramMappingPrecomp (F.map (singleIso d).hom) W

theorem nativeVertex (d : ℕ) (i : Fin (d + 1)) :
    pointAt (single d) (ULift.up i) ≫ (singleIso d).hom = vertex ⦋d⦌ i := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, pointAt_vertex, vertex, SSet.stdSimplex.yonedaEquiv_map]
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [singleIso_vertex, Equiv.apply_symm_apply]
  rfl

private theorem rowRestriction_vertex (W : Source) (d : ℕ) (i : Fin (d + 1)) :
    (rowRestrictionIso W ⦋d⦌).inv ≫ rowVertex W ⦋d⦌ i =
      W.map (ReverseSimplex.inclusion.map (SimplexCategory.const ⦋0⦌ ⦋d⦌ i)).op ≫
        (rowRestrictionIso W ⦋0⦌).inv := by
  apply NatTrans.ext
  funext q x
  dsimp [rowRestrictionIso, rowVertex, row,
    JTRealizationDiagonal.ordinaryCurry, JTReversalInput.ordinaryInput]
  simp

private theorem freeSimplexRowIso_vertex (W : Source) (d : ℕ) (i : Fin (d + 1)) :
    diagramMappingPrecomp (F.map (vertex ⦋d⦌ i)) W ≫ (freeSimplexRowIso W 0).hom =
      (freeSimplexRowIso W d).hom ≫ rowVertex W ⦋d⦌ i := by
  have h := freeSimplexMappingIso_natural W (SimplexCategory.const ⦋0⦌ ⦋d⦌ i)
  change diagramMappingPrecomp (F.map (vertex ⦋d⦌ i)) W ≫ (freeMappingIso W 0).hom =
      (freeMappingIso W d).hom ≫
        W.map (ReverseSimplex.inclusion.map (SimplexCategory.const ⦋0⦌ ⦋d⦌ i)).op at h
  simpa only [freeSimplexRowIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, rowRestriction_vertex] using
    congrArg (fun q ↦ q ≫ (rowRestrictionIso W ⦋0⦌).inv) h

/-- The whole native label restricts to the same original row face. -/
theorem labelFromRow_vertex (W : Source) (d : ℕ) (i : Fin (d + 1)) :
    labelFromRow W d ≫ diagramMappingPrecomp
      (F.map (pointAt (single d) (ULift.up i))) W =
      rowVertex W ⦋d⦌ i ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  have h := freeSimplexRowIso_vertex W d i
  have h' := congrArg (fun q ↦ (freeSimplexRowIso W d).inv ≫ q ≫
    (freeSimplexRowIso W 0).inv) h
  have hp :
      (freeSimplexRowIso W d).inv ≫ diagramMappingPrecomp (F.map (vertex ⦋d⦌ i)) W =
        rowVertex W ⦋d⦌ i ≫ (freeSimplexRowIso W 0).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
      Category.comp_id] using h'
  unfold labelFromRow TwoBeadEndpointLabel.jointLabelFromRow
  rw [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp, nativeVertex]
  exact hp

/-- The entire native single-bead realization is the original coend box map
transported along the native single-bead isomorphism. -/
theorem realized_nativeLabel (W : Source) (d : ℕ) (k : SimplexCategory)
    (f : SSet.stdSimplex.obj k ⟶ row W ⦋d⦌) :
    JTNecklaceLabelRealization.realizedLabel (single d).toSSet W k
        (SSet.yonedaEquiv (f ≫ labelFromRow W d)) =
      ((singleIso d).hom ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) ≫
        JTRealizationGenerators.generator (JTReversalInput.ordinaryInput.obj W)
          (⦋d⦌, k) (SSet.yonedaEquiv (X := row W ⦋d⦌) f) := by
  let w := SSet.yonedaEquiv (X := row W ⦋d⦌) f
  have h := JTNecklaceLabelRealization.realizedLabel_natural_X (singleIso d).hom W k
    (JTRowRealizationGenerator.rowCoefficient W d k w)
  rw [JTRowRealizationGenerator.realizedRowCoefficient_eq_generator] at h
  unfold labelFromRow
  rw [← Category.assoc, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  exact h.symm

end

end DaggerModels.PartII.JTNativeRowLabel
