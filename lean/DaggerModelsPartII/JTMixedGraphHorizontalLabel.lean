import DaggerModelsPartII.JTMixedGraphHorizontalTraversal
import DaggerModelsPartII.JTGraphToPresentationArrow

/-! Ordered labels of the actual three-bead graphs respect horizontal restriction. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphHorizontalLabel

open JTMixedGraphHorizontalTraversal JTMixedGraphEndpointLifts
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints OrderedSimplexEndpointFiber
open ReversalDiscreteFreeColimits
open JTProjectiveOrderedFiberComparison (row rowRestrictionIso)
open JTNativeRowLabel (labelFromRow)

noncomputable section

private abbrev F := discreteFree.{0}
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (n : SimplexCategory) := SSet.stdSimplex.{0}.obj n
private abbrev J := GroupoidSimplex.parameter
private abbrev rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev A := single 1
private abbrev code := MixedGraphCylinderTraversal.code
private abbrev L (d : ℕ) := tripleRightT.{0} A (single d) A
private abbrev M (d : ℕ) := tripleRightU.{0} A (single d) A
private abbrev R (d : ℕ) := tripleRightV.{0} A (single d) A

variable {d e : ℕ}

private theorem row_restriction (W : Source) (a : ⦋d⦌ ⟶ ⦋e⦌) :
    (rowRestrictionIso W ⦋e⦌).inv ≫ (rows W).map a.op =
      W.map (ReverseSimplex.inclusion.map a).op ≫ (rowRestrictionIso W ⦋d⦌).inv := by
  apply NatTrans.ext
  funext q x
  dsimp [rowRestrictionIso, rows, row,
    JTRealizationDiagonal.ordinaryCurry, JTReversalInput.ordinaryInput]
  simp

private theorem freeRow_natural (W : Source) (a : ⦋d⦌ ⟶ ⦋e⦌) :
    diagramMappingPrecomp (F.map (SSet.stdSimplex.map a)) W ≫ (freeSimplexRowIso W d).hom =
      (freeSimplexRowIso W e).hom ≫ (rows W).map a.op := by
  have h := freeSimplexMappingIso_natural W a
  change diagramMappingPrecomp (F.map (SSet.stdSimplex.map a)) W ≫ (freeMappingIso W d).hom =
    (freeMappingIso W e).hom ≫ W.map (ReverseSimplex.inclusion.map a).op at h
  simpa only [freeSimplexRowIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, row_restriction] using
    congrArg (fun g ↦ g ≫ (rowRestrictionIso W ⦋d⦌).inv) h

theorem labelFromRow_natural (W : Source) (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0) (h₁ : a.toOrderHom (Fin.last d) = Fin.last e) :
    labelFromRow W e ≫ diagramMappingPrecomp (F.map (singleOperator a h₀ h₁).map) W =
      (rows W).map a.op ≫ labelFromRow W d := by
  have h := congrArg (fun g ↦ (freeSimplexRowIso W e).inv ≫ g ≫
    (freeSimplexRowIso W d).inv) (freeRow_natural W a)
  have h' : (freeSimplexRowIso W e).inv ≫
        diagramMappingPrecomp (F.map (SSet.stdSimplex.map a)) W =
      (rows W).map a.op ≫ (freeSimplexRowIso W d).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] using h
  unfold labelFromRow
  rw [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp]
  change (freeSimplexRowIso W e).inv ≫
    diagramMappingPrecomp (F.map (((singleIso d).hom ≫ SSet.stdSimplex.map a ≫
      (singleIso e).inv) ≫ (singleIso e).hom)) W = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [F.map_comp, diagramMappingPrecomp_comp, ← Category.assoc, h', Category.assoc]

private abbrev labels (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  orderedNecklaceLabels W (boundaryPoint W x y)

private theorem orderedCoefficient_eq {W : Source} {T : NecklaceCode} {k : SimplexCategory}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} (z : ((labels W x y).obj (op T)).obj (op k)) :
    SSet.yonedaEquiv.symm (JTRealizedLabelEndpoints.orderedLabel W x y T k z) =
      SSet.yonedaEquiv.symm z ≫
        pullback.fst ((necklaceBoundaryRestriction W).app (op T)) (boundaryPoint W x y) := by
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, JTRealizedLabelEndpoints.orderedLabel]

private theorem coefficient_natural {W : Source} {T U : NecklaceCode} {k : SimplexCategory}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} (u : T ⟶ U)
    (z : ((labels W x y).obj (op U)).obj (op k)) :
    SSet.yonedaEquiv.symm (JTRealizedLabelEndpoints.orderedLabel W x y T k
      (((labels W x y).map u.op).app (op k) z)) =
    SSet.yonedaEquiv.symm (JTRealizedLabelEndpoints.orderedLabel W x y U k z) ≫
      diagramMappingPrecomp (F.map u.map) W := by
  have h : (labels W x y).map u.op ≫
        pullback.fst ((necklaceBoundaryRestriction W).app (op T)) (boundaryPoint W x y) =
      pullback.fst ((necklaceBoundaryRestriction W).app (op U)) (boundaryPoint W x y) ≫
        diagramMappingPrecomp (F.map u.map) W := by
    simp only [orderedNecklaceLabels, orderedLabelDiagram, pullback.map, pullback.lift_fst]
    rfl
  rw [orderedCoefficient_eq, orderedCoefficient_eq,
    ← SSet.yonedaEquiv_symm_comp z ((labels W x y).map u.op), Category.assoc, h]
  exact (Category.assoc _ _ _).symm

private theorem coefficient_injective {W : Source} {T : NecklaceCode} {k : SimplexCategory}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} :
    Function.Injective (fun z : ((labels W x y).obj (op T)).obj (op k) ↦
      SSet.yonedaEquiv.symm (JTRealizedLabelEndpoints.orderedLabel W x y T k z)) := by
  intro z z' h
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · simpa only [orderedCoefficient_eq] using h
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem threeBeadLabel_ext {W : Source} {k : SimplexCategory}
    {p q : Δ k ⟶ TripleBeadEndpointLabel.labels W (code d)}
    (hL : p ≫ diagramMappingPrecomp (F.map (L d)) W =
      q ≫ diagramMappingPrecomp (F.map (L d)) W)
    (hM : p ≫ diagramMappingPrecomp (F.map (M d)) W =
      q ≫ diagramMappingPrecomp (F.map (M d)) W)
    (hR : p ≫ diagramMappingPrecomp (F.map (R d)) W =
      q ≫ diagramMappingPrecomp (F.map (R d)) W) : p = q := by
  apply (TripleBeadEndpointLabel.wedgeMappingPullback W A (wedge (single d) A)).hom_ext
  · exact hL
  · apply (TripleBeadEndpointLabel.wedgeMappingPullback W (single d) A).hom_ext
    · simpa only [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp] using hM
    · simpa only [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp] using hR

/-- The original padded horizontal map restricts the whole ordered label. -/
theorem orderedPoint_horizontal {W : Source} {k : SimplexCategory} (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0) (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    {f : Δ k ⟶ row W ⦋e⦌} {s : Δ ⦋e⦌ ⟶ J.obj k}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} (E : EdgeFamilies W ⦋e⦌ k f s x y) :
    (((labels W x y).map (padded (singleOperator a h₀ h₁)).op).app (op k)
      (JTMixedGraphOrderedLabel.orderedPoint E)) =
    JTMixedGraphOrderedLabel.orderedPoint (restrictFamilies a h₀ h₁ E) := by
  apply coefficient_injective
  dsimp only
  rw [coefficient_natural]
  let B := restrictFamilies a h₀ h₁ E
  let C := SSet.yonedaEquiv.symm
    (JTRealizedLabelEndpoints.orderedLabel W x y (code e) k
      (JTMixedGraphOrderedLabel.orderedPoint E))
  let D := SSet.yonedaEquiv.symm
    (JTRealizedLabelEndpoints.orderedLabel W x y (code d) k
      (JTMixedGraphOrderedLabel.orderedPoint B))
  let pre {T U : SSet.{0}} (v : T ⟶ U) := diagramMappingPrecomp (F.map v) W
  change C ≫ pre (padded (singleOperator a h₀ h₁)).map = D
  have hLe : C ≫ pre (L e) = E.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W :=
    JTMixedGraphOrderedLabel.orderedPoint_left E
  have hLd : D ≫ pre (L d) = E.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W :=
    JTMixedGraphOrderedLabel.orderedPoint_left B
  have hMe : C ≫ pre (M e) = f ≫ labelFromRow W e :=
    JTMixedGraphOrderedLabel.orderedPoint_middle E
  have hMd : D ≫ pre (M d) = (f ≫ (rows W).map a.op) ≫ labelFromRow W d :=
    JTMixedGraphOrderedLabel.orderedPoint_middle B
  have hRe : C ≫ pre (R e) = E.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W :=
    JTMixedGraphOrderedLabel.orderedPoint_right E
  have hRd : D ≫ pre (R d) = E.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W :=
    JTMixedGraphOrderedLabel.orderedPoint_right B
  apply threeBeadLabel_ext
  · change (C ≫ pre (padded (singleOperator a h₀ h₁)).map) ≫ pre (L d) = D ≫ pre (L d)
    dsimp only [pre]
    rw [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp, padded_left]
    change C ≫ pre (L e) = D ≫ pre (L d)
    exact hLe.trans hLd.symm
  · change (C ≫ pre (padded (singleOperator a h₀ h₁)).map) ≫ pre (M d) = D ≫ pre (M d)
    dsimp only [pre]
    rw [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp, padded_middle,
      F.map_comp, diagramMappingPrecomp_comp, ← Category.assoc]
    change (C ≫ pre (M e)) ≫ pre (singleOperator a h₀ h₁).map = D ≫ pre (M d)
    rw [hMe, hMd, Category.assoc]
    dsimp only [pre]
    rw [labelFromRow_natural, ← Category.assoc]
  · change (C ≫ pre (padded (singleOperator a h₀ h₁)).map) ≫ pre (R d) = D ≫ pre (R d)
    dsimp only [pre]
    rw [Category.assoc, ← diagramMappingPrecomp_comp, ← F.map_comp, padded_right]
    change C ≫ pre (R e) = D ≫ pre (R d)
    exact hRe.trans hRd.symm

end

end DaggerModels.PartII.JTMixedGraphHorizontalLabel
