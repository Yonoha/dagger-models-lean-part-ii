import OrdinarySegalOrderedMappingFibres

/-!
# Iterated presentation of the unchanged ordered mapping fiber

The source endpoint is fixed first, then the target endpoint. The resulting
iterated pullback is canonically isomorphic to the original joint endpoint
fiber. Both endpoint vertices and their order remain literal.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalIteratedOrderedFiberIso

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres

noncomputable section

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op

private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

/-- Fix the original source vertex of a horizontal edge. -/
def sourceFiber (W : Space) (x : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (sourceFace W) (SSet.yonedaEquiv.symm x)

/-- The target face on edges with the original fixed source. -/
def targetOnSource (W : Space) (x : (row W 0).obj (op ⦋0⦌)) :
    sourceFiber W x ⟶ row W 0 :=
  pullback.fst (sourceFace W) (SSet.yonedaEquiv.symm x) ≫ targetFace W

/-- The iterated strict fiber at the same ordered vertices as `mappingFiber`. -/
def iteratedFiber (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (targetOnSource W x) (SSet.yonedaEquiv.symm y)

private def toSource (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ sourceFiber W x :=
  pullback.lift
    (pullback.fst (endpointArrow W) (endpointPoint W x y))
    (pullback.snd (endpointArrow W) (endpointPoint W x y)) (by
      have h := congrArg (fun z ↦ z ≫ prod.fst)
        (pullback.condition (f := endpointArrow W) (g := endpointPoint W x y))
      simpa only [Category.assoc, endpointArrow_fst, endpointPoint_fst] using h)

private def forward (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ iteratedFiber W x y :=
  pullback.lift (toSource W x y)
    (pullback.snd (endpointArrow W) (endpointPoint W x y)) (by
      have h := congrArg (fun z ↦ z ≫ prod.snd)
        (pullback.condition (f := endpointArrow W) (g := endpointPoint W x y))
      simpa only [targetOnSource, toSource, Category.assoc,
        pullback.lift_fst_assoc, endpointArrow_snd, endpointPoint_snd] using h)

private def backward (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    iteratedFiber W x y ⟶ mappingFiber W x y :=
  pullback.lift
    (pullback.fst (targetOnSource W x) (SSet.yonedaEquiv.symm y) ≫
      pullback.fst (sourceFace W) (SSet.yonedaEquiv.symm x))
    (pullback.snd (targetOnSource W x) (SSet.yonedaEquiv.symm y)) (by
      apply prod.hom_ext
      · have h := congrArg
          (fun z ↦ pullback.fst (targetOnSource W x)
            (SSet.yonedaEquiv.symm y) ≫ z)
          (pullback.condition (f := sourceFace W)
            (g := SSet.yonedaEquiv.symm x))
        have hzero : pullback.fst (targetOnSource W x)
            (SSet.yonedaEquiv.symm y) ≫
            pullback.snd (sourceFace W) (SSet.yonedaEquiv.symm x) =
            pullback.snd (targetOnSource W x) (SSet.yonedaEquiv.symm y) :=
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
        dsimp only at h
        rw [← Category.assoc
          (pullback.fst (targetOnSource W x) (SSet.yonedaEquiv.symm y))
          (pullback.snd (sourceFace W) (SSet.yonedaEquiv.symm x))
          (SSet.yonedaEquiv.symm x)] at h
        rw [hzero] at h
        simpa only [Category.assoc, endpointArrow_fst, endpointPoint_fst] using h
      · have h := pullback.condition (f := targetOnSource W x)
          (g := SSet.yonedaEquiv.symm y)
        simpa only [targetOnSource, Category.assoc,
          endpointArrow_snd, endpointPoint_snd] using h)

/-- Joint endpoint fiber equals the source-then-target iterated fiber. -/
def mappingFiberIso (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ≅ iteratedFiber W x y where
  hom := forward W x y
  inv := backward W x y
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [forward, backward, toSource]
    · simp [forward, backward]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [forward, backward, toSource]
      · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    · simp [forward, backward]

#print axioms mappingFiberIso

end
end DaggerModels.PartII.OrdinarySegalIteratedOrderedFiberIso
