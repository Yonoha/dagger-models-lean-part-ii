import DaggerModelsPartII.JTMixedGraphHorizontalLabel

/-! Row-label naturality for arbitrary unbased simplex operators, including triangle faces. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativeRowCoefficientOperators

open ReversalDiscreteFreeColimits (discreteFree)
open OrderedSimplexEndpointFiber (freeSimplexRowIso)
open JTProjectiveOrderedFiberComparison (row rowRestrictionIso)
open JTNativeRowLabel (labelFromRow)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev F := discreteFree.{0}
private abbrev std := SSet.stdSimplex.{0}

private theorem row_restriction (W : Source) (a : SimplexCategory) (b : SimplexCategory)
    (f : a ⟶ b) :
    (rowRestrictionIso W b).inv ≫ (Rows W).map f.op =
      W.map (ReverseSimplex.inclusion.map f).op ≫
        (rowRestrictionIso W a).inv := by
  apply NatTrans.ext
  funext q x
  dsimp [Rows, rowRestrictionIso, row,
    JTRealizationDiagonal.ordinaryCurry, JTReversalInput.ordinaryInput]
  simp

/-- The original free-simplex/row isomorphisms respect every ordinal operator. -/
theorem freeSimplexRowIso_natural (W : Source) {d e : ℕ} (a : ⦋d⦌ ⟶ ⦋e⦌) :
    diagramMappingPrecomp (F.map (std.map a)) W ≫ (freeSimplexRowIso W d).hom =
      (freeSimplexRowIso W e).hom ≫ (Rows W).map a.op := by
  have h := OrderedSimplexEndpointFiber.freeSimplexMappingIso_natural W a
  change diagramMappingPrecomp (F.map (std.map a)) W ≫
      (OrderedSimplexEndpointFiber.freeMappingIso W d).hom =
    (OrderedSimplexEndpointFiber.freeMappingIso W e).hom ≫
      W.map (ReverseSimplex.inclusion.map a).op at h
  simpa only [freeSimplexRowIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, row_restriction] using
    congrArg (fun g ↦ g ≫ (rowRestrictionIso W ⦋d⦌).inv) h

/-- Transport an arbitrary ordinal operator to the native simplicial sets.
It need not preserve the two global necklace endpoints. -/
def nativeOperator {d e : ℕ} (a : ⦋d⦌ ⟶ ⦋e⦌) :
    (single d).toSSet ⟶ (single e).toSSet :=
  (singleIso d).hom ≫ std.map a ≫ (singleIso e).inv

/-- Full row labels restrict along any simplex face, including the short
edges of a triangle which are not endpoint-preserving necklace arrows. -/
theorem labelFromRow_operator (W : Source) {d e : ℕ} (a : ⦋d⦌ ⟶ ⦋e⦌) :
    labelFromRow W e ≫ diagramMappingPrecomp (F.map (nativeOperator a)) W =
      (Rows W).map a.op ≫ labelFromRow W d := by
  have h := congrArg (fun g ↦ (freeSimplexRowIso W e).inv ≫ g ≫
    (freeSimplexRowIso W d).inv) (freeSimplexRowIso_natural W a)
  have h' : (freeSimplexRowIso W e).inv ≫ diagramMappingPrecomp (F.map (std.map a)) W =
      (Rows W).map a.op ≫ (freeSimplexRowIso W d).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
      Category.comp_id] using h
  unfold labelFromRow nativeOperator
  rw [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [F.map_comp, diagramMappingPrecomp_comp, ← Category.assoc, h', Category.assoc]

/-- The same identity for an arbitrary full coefficient simplex. -/
theorem coefficient_operator (W : Source) {d e : ℕ} {k : SimplexCategory}
    (a : ⦋d⦌ ⟶ ⦋e⦌) (c : std.obj k ⟶ row W ⦋e⦌) :
    (c ≫ labelFromRow W e) ≫ diagramMappingPrecomp (F.map (nativeOperator a)) W =
      (c ≫ (Rows W).map a.op) ≫ labelFromRow W d := by
  rw [Category.assoc, labelFromRow_operator, Category.assoc]

end
end DaggerModels.PartII.JTNativeRowCoefficientOperators
