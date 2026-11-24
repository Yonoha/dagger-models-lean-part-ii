import OrdinarySegalUnitSquares
import OrdinarySegalSpineTwoIncidence
import OrdinarySegalWalkingEvaluation
import DaggerModelsPartII.DiagramMappingPrecompFibration

/-!
# The actual binary Segal comparison on ordinary rows

The two shared-vertex maps of the geometric spine become the literal
`δ₁` and `δ₀` restrictions. Its strict pullback is transported to the
actual row pullback `W₁ ×_{W₀} W₁`, retaining the two outer face maps.
For an injectively Kan fibrant Segal space the resulting binary map is a
Kan trivial fibration. No ordinary completeness condition is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalBinaryComparison

open OrdinaryCSSLocalization OrdinarySegalSpineTwoPullback
open OrdinarySegalUnitSquares OrdinarySegalSpineTwoIncidence
open SpineOuterFacePushout

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private def d₁ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op

private def d₀ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

private theorem mapSpaceIso_hom {K L : SSet.{0}} (e : K ≅ L) (W : Space) :
    (mapSpaceIso e W).hom = diagramMappingPrecomp (discrete.map e.inv) W := rfl

private theorem mapSpaceIso_inv {K L : SSet.{0}} (e : K ≅ L) (W : Space) :
    (mapSpaceIso e W).inv = diagramMappingPrecomp (discrete.map e.hom) W := rfl

/-- The first transported shared-vertex operator is the literal first
vertex of the final edge. -/
theorem firstVertex_eq (W : Space) :
    firstVertex W = diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (1 : Fin 2))) W := by
  simp only [firstVertex, firstEdgeIso, commonVertexIso, mapSpaceIso_inv,
    mapSpaceIso_hom, ← diagramMappingPrecomp_comp, ← Functor.map_comp]
  rw [Category.assoc, first_incidence]

/-- The second transported shared-vertex operator is the literal final
vertex of the initial edge. -/
theorem lastVertex_eq (W : Space) :
    lastVertex W = diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (0 : Fin 2))) W := by
  simp only [lastVertex, lastEdgeIso, commonVertexIso, mapSpaceIso_inv,
    mapSpaceIso_hom, ← diagramMappingPrecomp_comp, ← Functor.map_comp]
  rw [Category.assoc, last_incidence]

/-- Both standard edges, glued at their literal shared vertex, yield
the actual horizontal row pullback. -/
def rowSpineIso (W : Space) :
    diagramMappingSpace
        (discrete.obj (DaggerNativeStandardSpineInner.spine 2 : SSet.{0})) W ≅
      pullback (d₁ W) (d₀ W) := by
  let e₀ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 0
  let e₁ := OrdinarySegalWalkingEvaluation.simplexMappingIso W 1
  have h₁ : firstVertex W ≫ e₀.hom = e₁.hom ≫ d₁ W := by
    rw [firstVertex_eq]
    exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
      (SimplexCategory.δ (1 : Fin 2))
  have h₀ : lastVertex W ≫ e₀.hom = e₁.hom ≫ d₀ W := by
    rw [lastVertex_eq]
    exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
      (SimplexCategory.δ (0 : Fin 2))
  let m := pullback.map (firstVertex W) (lastVertex W) (d₁ W) (d₀ W)
    e₁.hom e₁.hom e₀.hom h₁ h₀
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  exact spineTwoEdgesIso W ≪≫ asIso m

/-- The binary map from the actual degree-two row into the literal
composable-edge pullback. -/
def binaryComparison (W : Space) : row W 2 ⟶ pullback (d₁ W) (d₀ W) :=
  (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
    OrdinarySegalDegeneracyPullback.spineRestriction W ≫
      (rowSpineIso W).hom

/-- This is the actual pair `(d₀,d₂)` of outer faces. -/
theorem binaryComparison_fst (W : Space) :
    binaryComparison W ≫ pullback.fst (d₁ W) (d₀ W) =
      W.map (SimplexCategory.δ (0 : Fin 3)).op := by
  have hface : firstPartIso.inv ≫ (firstSpinePart.{0} 0).ι =
      SSet.stdSimplex.δ (0 : Fin 3) := by
    rw [← firstPart_face, Iso.inv_hom_id_assoc]
  calc
    binaryComparison W ≫ pullback.fst (d₁ W) (d₀ W) =
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
          OrdinarySegalDegeneracyPullback.spineRestriction W ≫
            ((spineTwoEdgesIso W).hom ≫
              pullback.fst (firstVertex W) (lastVertex W)) ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
          simp only [binaryComparison, rowSpineIso, Iso.trans_hom,
            asIso_hom, pullback.map, pullback.lift_fst, Category.assoc]
    _ = (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
          OrdinarySegalDegeneracyPullback.spineRestriction W ≫
            (diagramMappingPrecomp
              (discrete.map (SSet.Subcomplex.homOfLE
                (inf_le_left : firstSpinePart.{0} 0 ≤
                  DaggerNativeStandardSpineInner.spine 2))) W ≫
              (firstEdgeIso W).hom) ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
          rw [spineTwoEdgesIso_first]
    _ = (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
          diagramMappingPrecomp
            (discrete.map (SSet.stdSimplex.δ (0 : Fin 3))) W ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
          have hpre : OrdinarySegalDegeneracyPullback.spineRestriction W ≫
              (diagramMappingPrecomp
                (discrete.map (SSet.Subcomplex.homOfLE
                  (inf_le_left : firstSpinePart.{0} 0 ≤
                    DaggerNativeStandardSpineInner.spine 2))) W ≫
                (firstEdgeIso W).hom) =
              diagramMappingPrecomp (discrete.map (SSet.stdSimplex.δ (0 : Fin 3))) W := by
            dsimp only [OrdinarySegalDegeneracyPullback.spineRestriction,
              OrdinaryCSSLocalization.spineMap, firstEdgeIso]
            rw [mapSpaceIso_hom, ← diagramMappingPrecomp_comp,
              ← diagramMappingPrecomp_comp, ← discrete.map_comp, ← discrete.map_comp]
            rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
            exact congrArg (fun k ↦ diagramMappingPrecomp (discrete.map k) W) hface
          simpa only [Category.assoc] using congrArg
            (fun k ↦ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫ k ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom) hpre
    _ = W.map (SimplexCategory.δ (0 : Fin 3)).op := by
          change (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
              diagramMappingPrecomp
                (discrete.map (SSet.stdSimplex.map
                  (SimplexCategory.δ (0 : Fin 3)))) W ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom = _
          rw [OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
            (SimplexCategory.δ (0 : Fin 3))]
          simp only [Iso.inv_hom_id_assoc]

/-- This is the actual pair `(d₀,d₂)` of outer faces. -/
theorem binaryComparison_snd (W : Space) :
    binaryComparison W ≫ pullback.snd (d₁ W) (d₀ W) =
      W.map (SimplexCategory.δ (Fin.last 2)).op := by
  have hface : lastPartIso.inv ≫ (lastSpinePart.{0} 0).ι =
      DaggerOriginalCounitRightCone.face 1 := by
    rw [← lastPart_face, Iso.inv_hom_id_assoc]
  calc
    binaryComparison W ≫ pullback.snd (d₁ W) (d₀ W) =
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
          OrdinarySegalDegeneracyPullback.spineRestriction W ≫
            ((spineTwoEdgesIso W).hom ≫
              pullback.snd (firstVertex W) (lastVertex W)) ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
          simp only [binaryComparison, rowSpineIso, Iso.trans_hom,
            asIso_hom, pullback.map, pullback.lift_snd, Category.assoc]
    _ = (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
          OrdinarySegalDegeneracyPullback.spineRestriction W ≫
            (diagramMappingPrecomp
              (discrete.map (SSet.Subcomplex.homOfLE
                (inf_le_left : lastSpinePart.{0} 0 ≤
                  DaggerNativeStandardSpineInner.spine 2))) W ≫
              (lastEdgeIso W).hom) ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
          rw [spineTwoEdgesIso_last]
    _ = (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
          diagramMappingPrecomp
            (discrete.map (DaggerOriginalCounitRightCone.face 1)) W ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
          have hpre : OrdinarySegalDegeneracyPullback.spineRestriction W ≫
              (diagramMappingPrecomp
                (discrete.map (SSet.Subcomplex.homOfLE
                  (inf_le_left : lastSpinePart.{0} 0 ≤
                    DaggerNativeStandardSpineInner.spine 2))) W ≫
                (lastEdgeIso W).hom) =
              diagramMappingPrecomp (discrete.map (DaggerOriginalCounitRightCone.face 1)) W := by
            dsimp only [OrdinarySegalDegeneracyPullback.spineRestriction,
              OrdinaryCSSLocalization.spineMap, lastEdgeIso]
            rw [mapSpaceIso_hom, ← diagramMappingPrecomp_comp,
              ← diagramMappingPrecomp_comp, ← discrete.map_comp, ← discrete.map_comp]
            rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
            exact congrArg (fun k ↦ diagramMappingPrecomp (discrete.map k) W) hface
          simpa only [Category.assoc] using congrArg
            (fun k ↦ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫ k ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom) hpre
    _ = W.map (SimplexCategory.δ (Fin.last 2)).op := by
          change (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
              diagramMappingPrecomp
                (discrete.map (SSet.stdSimplex.map
                  (SimplexCategory.δ (Fin.last 2)))) W ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom = _
          rw [OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
            (SimplexCategory.δ (Fin.last 2))]
          simp only [Iso.inv_hom_id_assoc]

/-- Reedy-Kan fibrancy and the ordinary Segal condition make the literal
binary pair `(d₀,d₂)` a Kan trivial fibration. -/
theorem binaryComparison_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    Fibration (binaryComparison W) ∧ WeakEquivalence (binaryComparison W) := by
  haveI : Mono (spineMap 2) := spineMap_mono 2
  haveI : Fibration (OrdinarySegalDegeneracyPullback.spineRestriction W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration
      SimplexCategoryᵒᵖ (spineMap 2) W
  haveI : WeakEquivalence (OrdinarySegalDegeneracyPullback.spineRestriction W) :=
    (weakEquivalence_iff _).mpr (hSegal 2 (by decide))
  dsimp only [binaryComparison]
  exact ⟨inferInstance, inferInstance⟩

#print axioms firstVertex_eq
#print axioms lastVertex_eq
#print axioms rowSpineIso
#print axioms binaryComparison_fst
#print axioms binaryComparison_snd
#print axioms binaryComparison_trivialFibration

end

end DaggerModels.PartII.OrdinarySegalBinaryComparison
