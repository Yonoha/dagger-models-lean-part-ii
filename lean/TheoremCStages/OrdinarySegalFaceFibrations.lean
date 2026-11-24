import OrdinarySegalWalkingEvaluation

/-!
# Actual face fibrations of Kan-injectively fibrant ordinary simplicial spaces

Restriction along a horizontal coface is an actual Kan fibration on the
original rows, by the existing mapping-space lifting theorem and the checked
representable mapping isomorphism. No Segal or completeness hypothesis is used.
Together with the two literal unit-comparison weak equivalences, this verifies
that the strict pullbacks used in Rezk 12.4 compute homotopy pullbacks.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalFaceFibrations

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Every literal horizontal face operator is Kan fibrant on an injectively
Kan fibrant simplicial space. -/
theorem face_fibration (W : Space) [IsFibrant W] (n : ℕ) (i : Fin (n + 2)) :
    Fibration (W.map (SimplexCategory.δ i).op) := by
  let j : (Δ[n] : SSet.{0}) ⟶ Δ[n + 1] := SSet.stdSimplex.δ i
  have : Mono j := by
    dsimp only [j]
    rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    infer_instance
  have : Mono (discrete.map j) := OrdinaryCSSLocalization.discrete_map_mono j
  have hf : Fibration (diagramMappingPrecomp (discrete.map j) W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration SimplexCategoryᵒᵖ _ W
  let e : Arrow.mk (diagramMappingPrecomp (discrete.map j) W) ≅
      Arrow.mk (W.map (SimplexCategory.δ i).op) :=
    Arrow.isoMk
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W (n + 1))
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W n)
      (OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
        (SimplexCategory.δ i)).symm
  exact (fibration_iff _).mpr (((fibrations SSet.{0}).arrow_mk_iso_iff e).mp
    ((fibration_iff _).mp hf))

#print axioms face_fibration

end

end DaggerModels.PartII.OrdinarySegalFaceFibrations
