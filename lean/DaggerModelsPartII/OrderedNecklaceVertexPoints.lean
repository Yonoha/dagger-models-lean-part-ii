import DaggerModelsPartII.OrderedNecklaceLabelDiagram
import DaggerModelsPartII.JTProjectiveOrderedFiberComparison
import DaggerModelsPartII.RepresentableTensorAdjunction
import DaggerModelsPartII.DiagramMappingLimits

/-!
# Original ordered vertices as actual necklace-boundary labels

The point of the common boundary-label space is built from the original raw
zero-row vertices, using the retained tensor--Yoneda inverse and actual
coproduct universal property. No arbitrary endpoint point or evaluation formula
for a chosen right-adjoint-uniqueness isomorphism is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerModels

namespace DaggerModels.PartII.OrderedNecklaceVertexPoints

open SegalLocalizers ReversalDiscreteFreeColimits
open OrderedNecklaceLabelDiagram JTProjectiveOrderedFiberComparison

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}

/-- The original zero-row vertex as a literal zero-simplex of the free-zero
diagram mapping space, with the actual free/representable comparison. -/
def zeroLabel (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (diagramMappingSpace (F.obj (Δ[0] : SSet.{0})) W).obj (op ⦋0⦌) :=
  Functor.whiskerRight (SegalRepresentables.freeSimplexRepresentable 0).hom
      (tensorRight (Δ[0] : SSet.{0})) ≫
    representableTensorHomFrom (ReverseSimplex.inclusion.obj ⦋0⦌)
      (vertexPoint W x ≫ (rowRestrictionIso W ⦋0⦌).hom)

/-- The specified zero-row vertex supplies a point of the same literal
free-zero mapping space, without choosing a representative. -/
def zeroPoint (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (F.obj (Δ[0] : SSet.{0})) W :=
  SSet.yonedaEquiv.symm (zeroLabel W x)

/-- Transport back along the SAME free/representable isomorphism and evaluate
by the retained tensor--Yoneda equivalence: the original vertex is recovered. -/
theorem zeroLabel_tensorYoneda (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    representableTensorHomTo (ReverseSimplex.inclusion.obj ⦋0⦌)
      (Functor.whiskerRight (SegalRepresentables.freeSimplexRepresentable 0).inv
          (tensorRight (Δ[0] : SSet.{0})) ≫ zeroLabel W x) =
      vertexPoint W x ≫ (rowRestrictionIso W ⦋0⦌).hom := by
  unfold zeroLabel
  rw [← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id]
  simpa only [Functor.whiskerRight_id, Category.id_comp] using
    representableTensorHomTo_from (ReverseSimplex.inclusion.obj ⦋0⦌)
      (vertexPoint W x ≫ (rowRestrictionIso W ⦋0⦌).hom)

/-- Strict mapping spaces carry the actual ordered coproduct boundary to its
ordered binary product cone. -/
def boundaryMappingIsLimit (W : Source) :
    IsLimit (BinaryFan.mk
      (diagramMappingPrecomp
        (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W)
      (diagramMappingPrecomp
        (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W)) := by
  letI : PreservesLimitsOfShape (Discrete WalkingPair) (diagramMappingSource W) :=
    diagramMappingSource_preservesLimitsOfShape (Discrete WalkingPair) W
  have h := mapIsLimitOfPreservesOfIsLimit (diagramMappingSource W)
    (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary).op
    (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary).op
    (BinaryCofan.IsColimit.op
      (c := BinaryCofan.mk
        (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary)
        (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary))
      (coprodIsCoprod (F.obj (Δ[0] : SSet.{0})) (F.obj (Δ[0] : SSet.{0}))))
  change IsLimit (BinaryFan.mk
    (diagramMappingPrecomp
      (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W)
    (diagramMappingPrecomp
      (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W)) at h
  exact h

/-- The original boundary-label space, in zero--one product order. -/
def boundaryMappingIso (W : Source) :
    diagramMappingSpace boundary W ≅
      diagramMappingSpace (F.obj (Δ[0] : SSet.{0})) W ⨯
        diagramMappingSpace (F.obj (Δ[0] : SSet.{0})) W :=
  IsLimit.conePointUniqueUpToIso (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _))

theorem boundaryMappingIso_fst (W : Source) :
    (boundaryMappingIso W).hom ≫ prod.fst =
      diagramMappingPrecomp
        (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.left⟩

theorem boundaryMappingIso_snd (W : Source) :
    (boundaryMappingIso W).hom ≫ prod.snd =
      diagramMappingPrecomp
        (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (boundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.right⟩

/-- The actual ordered pair of raw zero-row vertices, as the point of the
common necklace-boundary label space used by the operator diagrams. -/
def boundaryPoint (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace boundary W :=
  prod.lift (zeroPoint W x) (zeroPoint W y) ≫ (boundaryMappingIso W).inv

theorem boundaryPoint_first (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    boundaryPoint W x y ≫ diagramMappingPrecomp
        (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = zeroPoint W x := by
  rw [← boundaryMappingIso_fst]
  simp only [boundaryPoint, Category.assoc, Iso.inv_hom_id_assoc, prod.lift_fst]

theorem boundaryPoint_last (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    boundaryPoint W x y ≫ diagramMappingPrecomp
        (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = zeroPoint W y := by
  rw [← boundaryMappingIso_snd]
  simp only [boundaryPoint, Category.assoc, Iso.inv_hom_id_assoc, prod.lift_snd]

end

end DaggerModels.PartII.OrderedNecklaceVertexPoints
