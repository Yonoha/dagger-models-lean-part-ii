import OrdinarySegalOrderedMappingFibres

/-!
# Target-first presentation of the unchanged ordered mapping fiber

The original target endpoint is fixed first and the source endpoint second.
The resulting iterated pullback is canonically isomorphic to the same
ordered mapping fiber defined by the joint endpoint arrow `(d₁,d₀)`.
All projections of the isomorphism are exposed at their literal endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalIteratedTargetFiberIso

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres

noncomputable section

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op

private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

/-- Fix the original target vertex of a horizontal edge. -/
def targetFiber (W : Space) (y : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (targetFace W) (SSet.yonedaEquiv.symm y)

/-- The source face on edges with the original fixed target. -/
def sourceOnTarget (W : Space) (y : (row W 0).obj (op ⦋0⦌)) :
    targetFiber W y ⟶ row W 0 :=
  pullback.fst (targetFace W) (SSet.yonedaEquiv.symm y) ≫ sourceFace W

/-- The target-then-source strict fiber at the same ordered vertices. -/
def iteratedFiber (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (sourceOnTarget W y) (SSet.yonedaEquiv.symm x)

/-- The first projection of the joint endpoint fiber fixes its exact target. -/
def toTarget (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ targetFiber W y :=
  pullback.lift
    (pullback.fst (endpointArrow W) (endpointPoint W x y))
    (pullback.snd (endpointArrow W) (endpointPoint W x y)) (by
      have h := congrArg (fun z ↦ z ≫ prod.snd)
        (pullback.condition (f := endpointArrow W) (g := endpointPoint W x y))
      simpa only [Category.assoc, endpointArrow_snd, endpointPoint_snd] using h)

private def forward (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ iteratedFiber W x y :=
  pullback.lift (toTarget W x y)
    (pullback.snd (endpointArrow W) (endpointPoint W x y)) (by
      have h := congrArg (fun z ↦ z ≫ prod.fst)
        (pullback.condition (f := endpointArrow W) (g := endpointPoint W x y))
      simpa only [sourceOnTarget, toTarget, Category.assoc,
        pullback.lift_fst_assoc, endpointArrow_fst, endpointPoint_fst] using h)

private def backward (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    iteratedFiber W x y ⟶ mappingFiber W x y :=
  pullback.lift
    (pullback.fst (sourceOnTarget W y) (SSet.yonedaEquiv.symm x) ≫
      pullback.fst (targetFace W) (SSet.yonedaEquiv.symm y))
    (pullback.snd (sourceOnTarget W y) (SSet.yonedaEquiv.symm x)) (by
      apply prod.hom_ext
      · have h := pullback.condition (f := sourceOnTarget W y)
          (g := SSet.yonedaEquiv.symm x)
        simpa only [sourceOnTarget, Category.assoc,
          endpointArrow_fst, endpointPoint_fst] using h
      · have h := congrArg
          (fun z ↦ pullback.fst (sourceOnTarget W y)
            (SSet.yonedaEquiv.symm x) ≫ z)
          (pullback.condition (f := targetFace W)
            (g := SSet.yonedaEquiv.symm y))
        have hzero : pullback.fst (sourceOnTarget W y)
            (SSet.yonedaEquiv.symm x) ≫
            pullback.snd (targetFace W) (SSet.yonedaEquiv.symm y) =
            pullback.snd (sourceOnTarget W y) (SSet.yonedaEquiv.symm x) :=
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
        dsimp only at h
        rw [← Category.assoc
          (pullback.fst (sourceOnTarget W y) (SSet.yonedaEquiv.symm x))
          (pullback.snd (targetFace W) (SSet.yonedaEquiv.symm y))
          (SSet.yonedaEquiv.symm y)] at h
        rw [hzero] at h
        simpa only [Category.assoc, endpointArrow_snd, endpointPoint_snd] using h)

/-- The unchanged ordered fiber equals the target-then-source fiber. -/
def mappingFiberIso (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ≅ iteratedFiber W x y where
  hom := forward W x y
  inv := backward W x y
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [forward, backward, toTarget]
    · simp [forward, backward]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [forward, backward, toTarget]
      · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    · simp [forward, backward]

/-- The forward map keeps the whole target-fixed edge coordinate. -/
theorem mappingFiberIso_hom_fst (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    (mappingFiberIso W x y).hom ≫
        pullback.fst (sourceOnTarget W y) (SSet.yonedaEquiv.symm x) =
      toTarget W x y := by
  simp [mappingFiberIso, forward]

/-- The forward map keeps the original point coordinate. -/
theorem mappingFiberIso_hom_snd (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    (mappingFiberIso W x y).hom ≫
        pullback.snd (sourceOnTarget W y) (SSet.yonedaEquiv.symm x) =
      pullback.snd (endpointArrow W) (endpointPoint W x y) := by
  simp [mappingFiberIso, forward]

/-- The inverse map keeps the literal row-one edge coordinate. -/
theorem mappingFiberIso_inv_fst (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    (mappingFiberIso W x y).inv ≫
        pullback.fst (endpointArrow W) (endpointPoint W x y) =
      pullback.fst (sourceOnTarget W y) (SSet.yonedaEquiv.symm x) ≫
        pullback.fst (targetFace W) (SSet.yonedaEquiv.symm y) := by
  simp [mappingFiberIso, backward]

/-- The inverse map keeps the original point coordinate. -/
theorem mappingFiberIso_inv_snd (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    (mappingFiberIso W x y).inv ≫
        pullback.snd (endpointArrow W) (endpointPoint W x y) =
      pullback.snd (sourceOnTarget W y) (SSet.yonedaEquiv.symm x) := by
  simp [mappingFiberIso, backward]

#print axioms mappingFiberIso
#print axioms mappingFiberIso_hom_fst
#print axioms mappingFiberIso_hom_snd
#print axioms mappingFiberIso_inv_fst
#print axioms mappingFiberIso_inv_snd

end
end DaggerModels.PartII.OrdinarySegalIteratedTargetFiberIso
