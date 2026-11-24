import DaggerModelsPartII.JTWalkingUnitaryWeak
import DaggerModelsPartII.ChosenHomotopyFiberFunctor
import DaggerModelsPartII.SegalSpaceConditions

/-! Unitary completeness compares the actual ordered walking-unitary
fibers with the homotopy fibers of the zero-row diagonal. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTUnitaryDiagonalPath

open SegalLocalizers JTWalkingUnitaryWeak
open ChosenHomotopyFiberComparison ChosenHomotopyFiberFunctor

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}

/-- The second vertex of the actual walking-unitary nerve. -/
def otherVertex : freeSimplex.{0} 0 ⟶ walkingUnitaryNerve.{0} :=
  (freeDaggerAdjunction.{0}.homEquiv (Δ[0] : SSet.{0}) walkingUnitaryNerve.{0}).symm
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₀ walkingOne.{0}))

/-- The second endpoint inclusion of the original reversal walking unitary. -/
def otherEndpoint : daggerSimplex.{0} 0 ⟶ walkingUnitarySpace.{0} :=
  discreteDagger.map otherVertex

theorem otherEndpoint_collapse :
    otherEndpoint ≫ collapseReverse = 𝟙 (daggerSimplex.{0} 0) := by
  unfold otherEndpoint collapseReverse
  rw [← Functor.map_comp, freeZeroIsTerminal.hom_ext (otherVertex ≫ collapseDagger) (𝟙 _)]
  exact discreteDagger.map_id _

variable (W : S)

abbrev Zero := diagramMappingSpace (daggerSimplex 0) W
abbrev Walking := diagramMappingSpace walkingUnitarySpace W

/-- Both original endpoint evaluations, in the order of their chosen vertices. -/
def unitaryEndpoints : Walking W ⟶ Zero W ⨯ Zero W :=
  prod.lift (diagramMappingPrecomp unitaryCompletenessMap W)
    (diagramMappingPrecomp otherEndpoint W)

/-- The literal diagonal of the original zero-simplex mapping space. -/
def diagonal : Zero W ⟶ Zero W ⨯ Zero W := prod.lift (𝟙 _) (𝟙 _)

/-- The constant coherent unitary induced by the original walking collapse. -/
def constantUnitary : Zero W ⟶ Walking W := diagramMappingPrecomp collapseReverse W

theorem constantUnitary_endpoints :
    constantUnitary W ≫ unitaryEndpoints W = diagonal W := by
  apply prod.hom_ext
  · simp only [unitaryEndpoints, diagonal, Category.assoc, prod.lift_fst, constantUnitary,
      ← diagramMappingPrecomp_comp, unitaryCompletenessMap_collapseReverse, diagramMappingPrecomp_id]
  · simp only [unitaryEndpoints, diagonal, Category.assoc, prod.lift_snd, constantUnitary,
      ← diagramMappingPrecomp_comp, otherEndpoint_collapse, diagramMappingPrecomp_id]

theorem constantUnitary_weak (hW : unitaryCompletenessCondition W) :
    WeakEquivalence (constantUnitary W) := by
  haveI : WeakEquivalence (diagramMappingPrecomp unitaryCompletenessMap W) :=
    (weakEquivalence_iff _).mpr hW
  exact weakEquivalence_of_postcomp_of_fac (show constantUnitary W ≫
      diagramMappingPrecomp unitaryCompletenessMap W = 𝟙 (Zero W) by
    rw [constantUnitary, ← diagramMappingPrecomp_comp,
      unitaryCompletenessMap_collapseReverse, diagramMappingPrecomp_id])

private theorem constant_square :
    diagonal W ≫ 𝟙 _ = constantUnitary W ≫ unitaryEndpoints W := by
  rw [Category.comp_id, constantUnitary_endpoints]

/-- The exact map of chosen homotopy fibers at any specified ordered pair. -/
def diagonalToUnitary (b : (Δ[0] : SSet.{0}) ⟶ Zero W ⨯ Zero W) :
    chosenFiber (diagonal W) b ⟶ chosenFiber (unitaryEndpoints W) b :=
  chosenMap (diagonal W) (unitaryEndpoints W) (constantUnitary W) (𝟙 _)
    (constant_square W) b b (Category.comp_id _)

/-- Completeness makes the diagonal-to-unitary comparison weak over the same point. -/
theorem diagonalToUnitary_weak (hW : unitaryCompletenessCondition W)
    (b : (Δ[0] : SSet.{0}) ⟶ Zero W ⨯ Zero W) :
    WeakEquivalence (diagonalToUnitary W b) := by
  let r := replacement (unitaryEndpoints W)
  letI : Fibration r.p := (fibration_iff _).mpr r.hp
  letI : WeakEquivalence r.i := (weakEquivalence_iff _).mpr r.hi.2
  letI := constantUnitary_weak W hW
  have h : diagonal W ≫ 𝟙 _ = (constantUnitary W ≫ r.i) ≫ r.p := by
    rw [Category.assoc, r.fac, constant_square]
  change WeakEquivalence (comparison (diagonal W) r.p (constantUnitary W ≫ r.i)
    (𝟙 _) h b b (Category.comp_id _))
  exact comparison_weak _ _ _ _ _ _ _ _

/-- The arrow induced on both zero-row coordinates by the actual diagram map. -/
def baseMap {V : S} (f : W ⟶ V) : Zero W ⨯ Zero W ⟶ Zero V ⨯ Zero V :=
  prod.map (diagramMappingPostcomp (daggerSimplex 0) f)
    (diagramMappingPostcomp (daggerSimplex 0) f)

private theorem precomp_postcomp {A B V : S} (a : A ⟶ B) (f : W ⟶ V) :
    diagramMappingPrecomp a W ≫ diagramMappingPostcomp A f =
      diagramMappingPostcomp B f ≫ diagramMappingPrecomp a V := by
  apply NatTrans.ext
  funext n z
  rfl

private theorem endpoints_natural {V : S} (f : W ⟶ V) :
    diagramMappingPostcomp walkingUnitarySpace f ≫ unitaryEndpoints V =
      unitaryEndpoints W ≫ baseMap W f := by
  apply prod.hom_ext
  · simp only [unitaryEndpoints, baseMap, Category.assoc, prod.lift_fst, prod.map_fst,
      prod.lift_fst_assoc]
    exact (precomp_postcomp W unitaryCompletenessMap f).symm
  · simp only [unitaryEndpoints, baseMap, Category.assoc, prod.lift_snd, prod.map_snd,
      prod.lift_snd_assoc]
    exact (precomp_postcomp W otherEndpoint f).symm

private theorem diagonal_natural {V : S} (f : W ⟶ V) :
    diagramMappingPostcomp (daggerSimplex 0) f ≫ diagonal V = diagonal W ≫ baseMap W f := by
  apply prod.hom_ext
  · simp [diagonal, baseMap]
  · simp [diagonal, baseMap]

private abbrev K := (Δ[0] : SSet.{0})

variable (b : K ⟶ Zero W ⨯ Zero W)

/-- The actual pointed diagonal and pointed walking endpoint arrows. -/
def pointedDiagonal : PointedArrow K := StructuredArrow.mk (Y := Arrow.mk (diagonal W)) b

def pointedUnitary : PointedArrow K := StructuredArrow.mk (Y := Arrow.mk (unitaryEndpoints W)) b

private def pointedConstant : pointedDiagonal W b ⟶ pointedUnitary W b :=
  StructuredArrow.homMk
    (Arrow.homMk (constantUnitary W) (𝟙 _) (constant_square W).symm) (Category.comp_id _)

/-- The pointed diagonal map induced by a diagram map. -/
def pointedDiagonalMap {V : S} (f : W ⟶ V) :
    pointedDiagonal W b ⟶ pointedDiagonal V (b ≫ baseMap W f) :=
  StructuredArrow.homMk
    (Arrow.homMk (diagramMappingPostcomp (daggerSimplex 0) f) (baseMap W f)
      (diagonal_natural W f)) rfl

/-- The pointed walking-unitary map induced by the same diagram map. -/
def pointedUnitaryMap {V : S} (f : W ⟶ V) :
    pointedUnitary W b ⟶ pointedUnitary V (b ≫ baseMap W f) :=
  StructuredArrow.homMk
    (Arrow.homMk (diagramMappingPostcomp walkingUnitarySpace f) (baseMap W f)
      (endpoints_natural W f)) rfl

/-- The actual constant comparison is natural in the target and specified point after localization. -/
theorem diagonalToUnitary_localized_natural {V : S} (f : W ⟶ V) :
    (weakEquivalences SSet.{0}).Q.map (diagonalToUnitary W b) ≫
        (localizedFiberFunctor K).map (pointedUnitaryMap W b f) =
      (localizedFiberFunctor K).map (pointedDiagonalMap W b f) ≫
        (weakEquivalences SSet.{0}).Q.map (diagonalToUnitary V (b ≫ baseMap W f)) := by
  change (localizedFiberFunctor K).map (pointedConstant W b) ≫
      (localizedFiberFunctor K).map (pointedUnitaryMap W b f) =
    (localizedFiberFunctor K).map (pointedDiagonalMap W b f) ≫
      (localizedFiberFunctor K).map (pointedConstant V (b ≫ baseMap W f))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end

end DaggerModels.PartII.JTUnitaryDiagonalPath
