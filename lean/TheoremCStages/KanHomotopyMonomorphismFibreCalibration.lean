import KanHomotopyMonomorphismFibre

/-!
# Calibrating the paired-base fiber to the exact fiber-map self-pullback

Both sides use the same original vertex `b` and the exact native `fibreMap`.
The comparison is an isomorphism of the actual strict pullback objects.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.KanHomotopyMonomorphismFibreCalibration

noncomputable section

open KanHomotopyMonomorphism (diagonal)
open KanHomotopyMonomorphismFibre (pairedBase)

variable {X Y A B : SSet.{0}} (p : X ⟶ A) (q : Y ⟶ B)
    (f : X ⟶ Y) (g : A ⟶ B) (h : p ≫ g = f ≫ q)
    (b : (Δ[0] : SSet.{0}) ⟶ A)

/-- The unchanged actual vertex-fiber map of the original square. -/
def exactFibreMap : pullback p b ⟶ pullback q (b ≫ g) :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap p q f g h b (b ≫ g) rfl

private def firstFiber :
    pullback (pairedBase p q f g h) (b ≫ diagonal g) ⟶ pullback p b :=
  pullback.lift
    (pullback.fst (pairedBase p q f g h) (b ≫ diagonal g) ≫ pullback.fst f f)
    (pullback.snd (pairedBase p q f g h) (b ≫ diagonal g))
    (by
      have hc := congrArg (fun t => t ≫ pullback.fst g g)
        (pullback.condition (f := pairedBase p q f g h)
          (g := b ≫ diagonal g))
      simpa [pairedBase, diagonal, Category.assoc] using hc)

private def secondFiber :
    pullback (pairedBase p q f g h) (b ≫ diagonal g) ⟶ pullback p b :=
  pullback.lift
    (pullback.fst (pairedBase p q f g h) (b ≫ diagonal g) ≫ pullback.snd f f)
    (pullback.snd (pairedBase p q f g h) (b ≫ diagonal g))
    (by
      have hc := congrArg (fun t => t ≫ pullback.snd g g)
        (pullback.condition (f := pairedBase p q f g h)
          (g := b ≫ diagonal g))
      simpa [pairedBase, diagonal, Category.assoc] using hc)

private theorem firstSecond_equal :
    firstFiber p q f g h b ≫ exactFibreMap p q f g h b =
      secondFiber p q f g h b ≫ exactFibreMap p q f g h b := by
  apply pullback.hom_ext
  · have hc := congrArg
      (fun t => pullback.fst (pairedBase p q f g h) (b ≫ diagonal g) ≫ t)
      (pullback.condition (f := f) (g := f))
    simpa [firstFiber, secondFiber, exactFibreMap,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap,
      Category.assoc] using hc
  · simp [firstFiber, secondFiber, exactFibreMap,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap, Category.assoc]

private def toSelfPullback :
    pullback (pairedBase p q f g h) (b ≫ diagonal g) ⟶
      pullback (exactFibreMap p q f g h b) (exactFibreMap p q f g h b) :=
  pullback.lift (firstFiber p q f g h b) (secondFiber p q f g h b)
    (firstSecond_equal p q f g h b)

private def pairOfFibers :
    pullback (exactFibreMap p q f g h b) (exactFibreMap p q f g h b) ⟶
      pullback f f :=
  pullback.lift
    (pullback.fst (exactFibreMap p q f g h b) (exactFibreMap p q f g h b) ≫
      pullback.fst p b)
    (pullback.snd (exactFibreMap p q f g h b) (exactFibreMap p q f g h b) ≫
      pullback.fst p b)
    (by
      have hc := congrArg (fun t => t ≫ pullback.fst q (b ≫ g))
        (pullback.condition (f := exactFibreMap p q f g h b)
          (g := exactFibreMap p q f g h b))
      simpa [exactFibreMap,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap,
        Category.assoc] using hc)

private def fromSelfPullback :
    pullback (exactFibreMap p q f g h b) (exactFibreMap p q f g h b) ⟶
      pullback (pairedBase p q f g h) (b ≫ diagonal g) :=
  pullback.lift (pairOfFibers p q f g h b)
    (pullback.fst (exactFibreMap p q f g h b) (exactFibreMap p q f g h b) ≫
      pullback.snd p b)
    (by
      apply pullback.hom_ext
      · have hc := congrArg
          (fun t => pullback.fst (exactFibreMap p q f g h b)
            (exactFibreMap p q f g h b) ≫ t)
          (pullback.condition (f := p) (g := b))
        simpa [pairOfFibers, pairedBase, diagonal, Category.assoc] using hc
      · have hpoint :
          (pullback.fst (exactFibreMap p q f g h b)
              (exactFibreMap p q f g h b) ≫ pullback.snd p b) =
            (pullback.snd (exactFibreMap p q f g h b)
              (exactFibreMap p q f g h b) ≫ pullback.snd p b) :=
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
        have hc := congrArg
          (fun t => pullback.snd (exactFibreMap p q f g h b)
            (exactFibreMap p q f g h b) ≫ t)
          (pullback.condition (f := p) (g := b))
        simpa [pairOfFibers, pairedBase, diagonal, Category.assoc,
          hpoint] using hc)

/-- The strict paired-base vertex fiber is exactly the self-pullback of the
unchanged original fiber map. -/
def selfPullbackIso :
    pullback (pairedBase p q f g h) (b ≫ diagonal g) ≅
      pullback (exactFibreMap p q f g h b) (exactFibreMap p q f g h b) where
  hom := toSelfPullback p q f g h b
  inv := fromSelfPullback p q f g h b
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [toSelfPullback, fromSelfPullback, pairOfFibers, firstFiber]
      · simp [toSelfPullback, fromSelfPullback, pairOfFibers, secondFiber]
    · simp [toSelfPullback, fromSelfPullback, firstFiber]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [toSelfPullback, fromSelfPullback, pairOfFibers, firstFiber]
      · simp [toSelfPullback, fromSelfPullback, firstFiber]
    · apply pullback.hom_ext
      · simp [toSelfPullback, fromSelfPullback, pairOfFibers, secondFiber]
      · simp [toSelfPullback, fromSelfPullback, secondFiber]
        exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The weak paired-base fiber map is the strict diagonal after the exact
pullback calibration. -/
theorem diagonal_calibration :
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      p (pairedBase p q f g h) (diagonal f) (diagonal g)
      (by
        apply pullback.hom_ext
        · simp [diagonal, pairedBase, Category.assoc]
        · simp [diagonal, pairedBase, Category.assoc])
      b (b ≫ diagonal g) rfl ≫ (selfPullbackIso p q f g h b).hom =
      diagonal (exactFibreMap p q f g h b) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [selfPullbackIso, toSelfPullback, firstFiber, diagonal,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap]
    · simp [selfPullbackIso, toSelfPullback, firstFiber, diagonal,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap]
  · apply pullback.hom_ext
    · simp [selfPullbackIso, toSelfPullback, secondFiber, diagonal,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap]
    · simp [selfPullbackIso, toSelfPullback, secondFiber, diagonal,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap]

/-- Weak strict diagonals on the two original levels induce a weak strict
diagonal on the exact original vertex-fiber map. -/
theorem exactFibreMap_diagonal_weak [Fibration p] [Fibration q]
    (hc : Fibration (KanHomotopyMonomorphismFibre.corner p q f g h))
    [WeakEquivalence (diagonal f)] [WeakEquivalence (diagonal g)] :
    WeakEquivalence (diagonal (exactFibreMap p q f g h b)) := by
  have hw := KanHomotopyMonomorphismFibre.diagonal_fiberMap_weak
    p q f g h b hc
  rw [← diagonal_calibration p q f g h b]
  letI := hw
  infer_instance

#print axioms selfPullbackIso
#print axioms diagonal_calibration
#print axioms exactFibreMap_diagonal_weak

end
end DaggerModels.PartII.KanHomotopyMonomorphismFibreCalibration
