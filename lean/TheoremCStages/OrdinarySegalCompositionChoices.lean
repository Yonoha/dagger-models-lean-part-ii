import OrdinarySegalOrderedMappingFibres
import OrdinarySegalBinaryComparison
import TopCatModelCategory.ModelCategorySSet

/-!
# The actual binary composition correspondence at fixed ordered vertices

For vertices `x,y,z`, pull the literal binary Segal comparison back along
the pair of strict ordered mapping fibers `map(y,z) × map(x,y)`. The resulting
space parametrizes all coherent two-simplex choices. Its projection to the
edge pair is a Kan trivial fibration, while its middle face lands in the
literal fiber `map(x,z)`. Thus composition is a derived span with its exact
original endpoints. No choice of a strict composition map or associativity
claim is made here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCompositionChoices

open OrdinaryCSSLocalization OrdinarySegalOrderedMappingFibres
open OrdinarySegalBinaryComparison

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op
private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op
private abbrev firstOuterFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (0 : Fin 3)).op
private abbrev middleFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op
private abbrev lastOuterFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (Fin.last 2)).op

/-- The original one-edge projection of a strict ordered fiber. -/
def fiberEdge (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ row W 1 :=
  pullback.fst (endpointArrow W) (endpointPoint W x y)

private def fiberVertex (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶ (Δ[0] : SSet.{0}) :=
  pullback.snd (endpointArrow W) (endpointPoint W x y)

theorem fiberEdge_source (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) :
    fiberEdge W x y ≫ sourceFace W =
      fiberVertex W x y ≫ SSet.yonedaEquiv.symm x := by
  calc
    fiberEdge W x y ≫ sourceFace W =
        (fiberEdge W x y ≫ endpointArrow W) ≫ prod.fst := by
          rw [Category.assoc, endpointArrow_fst]
    _ = (fiberVertex W x y ≫ endpointPoint W x y) ≫ prod.fst := by
          rw [fiberEdge, fiberVertex, pullback.condition]
    _ = fiberVertex W x y ≫ SSet.yonedaEquiv.symm x := by
          rw [Category.assoc, endpointPoint_fst]

theorem fiberEdge_target (W : Space) (x y : (row W 0).obj (op ⦋0⦌)) :
    fiberEdge W x y ≫ targetFace W =
      fiberVertex W x y ≫ SSet.yonedaEquiv.symm y := by
  calc
    fiberEdge W x y ≫ targetFace W =
        (fiberEdge W x y ≫ endpointArrow W) ≫ prod.snd := by
          rw [Category.assoc, endpointArrow_snd]
    _ = (fiberVertex W x y ≫ endpointPoint W x y) ≫ prod.snd := by
          rw [fiberEdge, fiberVertex, pullback.condition]
    _ = fiberVertex W x y ≫ SSet.yonedaEquiv.symm y := by
          rw [Category.assoc, endpointPoint_snd]

/-- The pair is ordered as final edge, initial edge, matching `(d₀,d₂)`. -/
def edgePair (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  mappingFiber W y z ⨯ mappingFiber W x y

private def finalEdge (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) : edgePair W x y z ⟶ row W 1 :=
  prod.fst ≫ fiberEdge W y z

private def initialEdge (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) : edgePair W x y z ⟶ row W 1 :=
  prod.snd ≫ fiberEdge W x y

/-- The common middle endpoint is the same actual vertex `y`. -/
private theorem pair_middle (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    finalEdge W x y z ≫ sourceFace W =
      initialEdge W x y z ≫ targetFace W := by
  calc
    finalEdge W x y z ≫ sourceFace W =
        (prod.fst : edgePair W x y z ⟶ mappingFiber W y z) ≫
          fiberVertex W y z ≫ SSet.yonedaEquiv.symm y := by
            rw [finalEdge, Category.assoc, fiberEdge_source]
    _ = (prod.snd : edgePair W x y z ⟶ mappingFiber W x y) ≫
          fiberVertex W x y ≫ SSet.yonedaEquiv.symm y := by
            exact congrArg (fun t ↦ t ≫ SSet.yonedaEquiv.symm y)
              (SSet.stdSimplex.objZeroIsTerminal.hom_ext
                (prod.fst ≫ fiberVertex W y z) (prod.snd ≫ fiberVertex W x y))
    _ = initialEdge W x y z ≫ targetFace W := by
          rw [initialEdge, Category.assoc, fiberEdge_target]

/-- The exact composable-edge point of the binary Segal pullback. -/
def pairToComposable (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    edgePair W x y z ⟶ pullback (sourceFace W) (targetFace W) :=
  pullback.lift (finalEdge W x y z) (initialEdge W x y z)
    (pair_middle W x y z)

/-- The full space of two-simplex choices over the fixed ordered edge pair. -/
def choices (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (binaryComparison W) (pairToComposable W x y z)

/-- Forget the two-simplex, retaining both original ordered edges. -/
def forgetChoice (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    choices W x y z ⟶ edgePair W x y z :=
  pullback.snd (binaryComparison W) (pairToComposable W x y z)

theorem forgetChoice_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    Fibration (forgetChoice W x y z) ∧ WeakEquivalence (forgetChoice W x y z) := by
  have hq := binaryComparison_trivialFibration W hSegal
  letI : Fibration (binaryComparison W) := hq.1
  letI : WeakEquivalence (binaryComparison W) := hq.2
  constructor
  · dsimp [forgetChoice, choices]
    infer_instance
  · exact SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback
      (IsPullback.of_hasPullback (binaryComparison W) (pairToComposable W x y z))

private theorem map_op_comp (W : Space) {a b c : SimplexCategory}
    (f : a ⟶ b) (g : b ⟶ c) :
    W.map g.op ≫ W.map f.op = W.map (f ≫ g).op := by
  rw [op_comp, Functor.map_comp]

private theorem middle_source (W : Space) :
    middleFace W ≫ sourceFace W = lastOuterFace W ≫ sourceFace W := by
  have h : SimplexCategory.δ (1 : Fin 2) ≫
        SimplexCategory.δ (1 : Fin 3) =
      SimplexCategory.δ (1 : Fin 2) ≫
        SimplexCategory.δ (Fin.last 2) := by
    ext i
    fin_cases i
    rfl
  calc
    middleFace W ≫ sourceFace W =
        W.map (SimplexCategory.δ (1 : Fin 2) ≫
          SimplexCategory.δ (1 : Fin 3)).op := map_op_comp W _ _
    _ = W.map (SimplexCategory.δ (1 : Fin 2) ≫
          SimplexCategory.δ (Fin.last 2)).op := by rw [h]
    _ = lastOuterFace W ≫ sourceFace W := (map_op_comp W _ _).symm

private theorem middle_target (W : Space) :
    middleFace W ≫ targetFace W = firstOuterFace W ≫ targetFace W := by
  have h : SimplexCategory.δ (0 : Fin 2) ≫
        SimplexCategory.δ (1 : Fin 3) =
      SimplexCategory.δ (0 : Fin 2) ≫
        SimplexCategory.δ (0 : Fin 3) := by
    ext i
    fin_cases i
    rfl
  calc
    middleFace W ≫ targetFace W =
        W.map (SimplexCategory.δ (0 : Fin 2) ≫
          SimplexCategory.δ (1 : Fin 3)).op := map_op_comp W _ _
    _ = W.map (SimplexCategory.δ (0 : Fin 2) ≫
          SimplexCategory.δ (0 : Fin 3)).op := by rw [h]
    _ = firstOuterFace W ≫ targetFace W := (map_op_comp W _ _).symm

/-- The actual middle face of every chosen two-simplex. -/
def compositeEdge (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) : choices W x y z ⟶ row W 1 :=
  pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫ middleFace W

private theorem chosen_finalEdge (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫
        firstOuterFace W =
      forgetChoice W x y z ≫ finalEdge W x y z := by
  calc
    _ = (pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫
          binaryComparison W) ≫ pullback.fst (sourceFace W) (targetFace W) := by
            exact congrArg
              (fun t ↦ pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫ t)
              (binaryComparison_fst W).symm
    _ = (forgetChoice W x y z ≫ pairToComposable W x y z) ≫
          pullback.fst (sourceFace W) (targetFace W) := by
            rw [pullback.condition]
            rfl
    _ = forgetChoice W x y z ≫ finalEdge W x y z := by
          rw [Category.assoc, pairToComposable, pullback.lift_fst]

private theorem chosen_initialEdge (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫
        lastOuterFace W =
      forgetChoice W x y z ≫ initialEdge W x y z := by
  calc
    _ = (pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫
          binaryComparison W) ≫ pullback.snd (sourceFace W) (targetFace W) := by
            exact congrArg
              (fun t ↦ pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫ t)
              (binaryComparison_snd W).symm
    _ = (forgetChoice W x y z ≫ pairToComposable W x y z) ≫
          pullback.snd (sourceFace W) (targetFace W) := by
            rw [pullback.condition]
            rfl
    _ = forgetChoice W x y z ≫ initialEdge W x y z := by
          rw [Category.assoc, pairToComposable, pullback.lift_snd]

/-- The chosen middle edge begins at the original vertex `x`. -/
theorem compositeEdge_source (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    compositeEdge W x y z ≫ sourceFace W =
      SSet.stdSimplex.objZeroIsTerminal.from _ ≫ SSet.yonedaEquiv.symm x := by
  calc
    compositeEdge W x y z ≫ sourceFace W =
        pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫
          lastOuterFace W ≫ sourceFace W := by
            rw [compositeEdge, Category.assoc, middle_source]
    _ = forgetChoice W x y z ≫ initialEdge W x y z ≫ sourceFace W := by
          simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ sourceFace W)
            (chosen_initialEdge W x y z)
    _ = forgetChoice W x y z ≫ prod.snd ≫
          fiberVertex W x y ≫ SSet.yonedaEquiv.symm x := by
            rw [initialEdge, Category.assoc, fiberEdge_source]
    _ = SSet.stdSimplex.objZeroIsTerminal.from _ ≫
          SSet.yonedaEquiv.symm x := by
            exact congrArg (fun t ↦ t ≫ SSet.yonedaEquiv.symm x)
              (SSet.stdSimplex.objZeroIsTerminal.hom_ext
                (forgetChoice W x y z ≫ prod.snd ≫ fiberVertex W x y)
                (SSet.stdSimplex.objZeroIsTerminal.from _))

/-- The chosen middle edge ends at the original vertex `z`. -/
theorem compositeEdge_target (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    compositeEdge W x y z ≫ targetFace W =
      SSet.stdSimplex.objZeroIsTerminal.from _ ≫ SSet.yonedaEquiv.symm z := by
  calc
    compositeEdge W x y z ≫ targetFace W =
        pullback.fst (binaryComparison W) (pairToComposable W x y z) ≫
          firstOuterFace W ≫ targetFace W := by
            rw [compositeEdge, Category.assoc, middle_target]
    _ = forgetChoice W x y z ≫ finalEdge W x y z ≫ targetFace W := by
          simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ targetFace W)
            (chosen_finalEdge W x y z)
    _ = forgetChoice W x y z ≫ prod.fst ≫
          fiberVertex W y z ≫ SSet.yonedaEquiv.symm z := by
            rw [finalEdge, Category.assoc, fiberEdge_target]
    _ = SSet.stdSimplex.objZeroIsTerminal.from _ ≫
          SSet.yonedaEquiv.symm z := by
            exact congrArg (fun t ↦ t ≫ SSet.yonedaEquiv.symm z)
              (SSet.stdSimplex.objZeroIsTerminal.hom_ext
                (forgetChoice W x y z ≫ prod.fst ≫ fiberVertex W y z)
                (SSet.stdSimplex.objZeroIsTerminal.from _))

/-- Binary composition is the actual middle-face map to `map(x,z)`, with
the complete contractible space of two-simplex choices retained. -/
def composite (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    choices W x y z ⟶ mappingFiber W x z :=
  pullback.lift (compositeEdge W x y z)
    (SSet.stdSimplex.objZeroIsTerminal.from _) (by
      apply prod.hom_ext
      · rw [Category.assoc, endpointArrow_fst,
          Category.assoc, endpointPoint_fst]
        exact compositeEdge_source W x y z
      · rw [Category.assoc, endpointArrow_snd,
          Category.assoc, endpointPoint_snd]
        exact compositeEdge_target W x y z)

theorem composite_edge (W : Space)
    (x y z : (row W 0).obj (op ⦋0⦌)) :
    composite W x y z ≫ fiberEdge W x z = compositeEdge W x y z :=
  pullback.lift_fst _ _ _

#print axioms fiberEdge_source
#print axioms fiberEdge_target
#print axioms pairToComposable
#print axioms forgetChoice_trivialFibration
#print axioms compositeEdge_source
#print axioms compositeEdge_target
#print axioms composite_edge

end

end DaggerModels.PartII.OrdinarySegalCompositionChoices
