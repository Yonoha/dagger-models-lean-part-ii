import OrdinaryCSSConditions
import DaggerModelsPartII.DiagramMappingPrecompFibration
import TopCatModelCategory.ModelCategorySSet

/-!
# Degree-two Segal pullbacks along the two degeneracies

The degree-two spine map is a trivial Kan fibration on mapping spaces when
the ordinary simplicial space is injectively fibrant and satisfies the strict
Segal condition. Pulling it back along either actual simplex degeneracy gives
a strict pullback whose canonical section is a Kan weak equivalence.

This is the model-category part of Rezk's Lemma 12.4. Identifying these
mapping-space pullbacks with the two displayed face-degeneracy squares is a
separate geometric comparison, not asserted by this module.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalDegeneracyPullback

noncomputable section

private abbrev Space := OrdinaryCSSLocalization.Space
private abbrev spineTwo := (DaggerNativeStandardSpineInner.spine 2).toSSet

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Either of the two actual degree-two simplex degeneracies. -/
def simplexDegeneracy (i : Fin 2) : (Δ[2] : SSet.{0}) ⟶ (Δ[1] : SSet.{0}) :=
  SSet.stdSimplex.map (SimplexCategory.σ i)

/-- The degree-two Segal restriction on the actual ordinary mapping space. -/
def spineRestriction (W : Space) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj (Δ[2] : SSet.{0})) W ⟶
      diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj spineTwo) W :=
  diagramMappingPrecomp (OrdinaryCSSLocalization.spineMap 2) W

/-- The degeneracy restricted to the complete degree-two spine. -/
def restrictedDegeneracy (i : Fin 2) (W : Space) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj (Δ[1] : SSet.{0})) W ⟶
      diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj spineTwo) W :=
  diagramMappingPrecomp
    (OrdinaryCSSLocalization.discrete.map
      ((DaggerNativeStandardSpineInner.spine 2).ι ≫ simplexDegeneracy i)) W

private def wholeDegeneracy (i : Fin 2) (W : Space) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj (Δ[1] : SSet.{0})) W ⟶
      diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj (Δ[2] : SSet.{0})) W :=
  diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map (simplexDegeneracy i)) W

private theorem degeneracy_restriction (i : Fin 2) (W : Space) :
    wholeDegeneracy i W ≫ spineRestriction W = restrictedDegeneracy i W := by
  dsimp [wholeDegeneracy, spineRestriction, restrictedDegeneracy]
  rw [← diagramMappingPrecomp_comp]
  rw [OrdinaryCSSLocalization.spineMap, ← Functor.map_comp]

/-- The canonical comparison from the degree-one mapping space to the
strict pullback of the degree-two Segal map along a degeneracy. -/
def comparison (i : Fin 2) (W : Space) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj (Δ[1] : SSet.{0})) W ⟶
      pullback (spineRestriction W) (restrictedDegeneracy i W) :=
  pullback.lift (wholeDegeneracy i W) (𝟙 _)
    (degeneracy_restriction i W)

theorem comparison_snd (i : Fin 2) (W : Space) :
    comparison i W ≫ pullback.snd (spineRestriction W) (restrictedDegeneracy i W) =
      𝟙 _ := by
  simp only [comparison, pullback.lift_snd]

/-- Reedy-Kan fibrancy and the actual degree-two Segal condition imply
weakness of both strict degeneracy-pullback comparisons. -/
theorem comparison_weak (i : Fin 2) (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (comparison i W) := by
  haveI : Mono (OrdinaryCSSLocalization.spineMap 2) :=
    OrdinaryCSSLocalization.spineMap_mono 2
  haveI : Fibration (spineRestriction W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration
      SimplexCategoryᵒᵖ (OrdinaryCSSLocalization.spineMap 2) W
  haveI : WeakEquivalence (spineRestriction W) :=
    (weakEquivalence_iff _).mpr (hSegal 2 (by decide))
  haveI : WeakEquivalence
      (pullback.snd (spineRestriction W) (restrictedDegeneracy i W)) :=
    SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback
      (IsPullback.of_hasPullback (spineRestriction W) (restrictedDegeneracy i W))
  exact weakEquivalence_of_postcomp_of_fac (comparison_snd i W)

#print axioms comparison_snd
#print axioms comparison_weak

end

end DaggerModels.PartII.OrdinarySegalDegeneracyPullback
