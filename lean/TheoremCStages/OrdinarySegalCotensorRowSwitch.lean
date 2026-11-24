import OrdinarySegalCotensorMappingIso
import OrdinarySegalWalkingEvaluation

/-!
# Switching the two original horizontal parameters

Braiding and the checked strict Fubini isomorphism identify an actual row
of the horizontal cotensor with a diagram mapping space into the cotensor
by that row's standard simplex. The comparison retains parameter maps,
including the original directed edge of the walking isomorphism.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalCotensorRowSwitch

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre)

noncomputable section

/-- Precomposition by the original simplicial braiding, as an isomorphism
of the exact diagram mapping spaces. -/
def braidMappingIso (K L : SSet.{0}) (W : Space) :
    diagramMappingSpace (discrete.obj (K ⊗ L)) W ≅
      diagramMappingSpace (discrete.obj (L ⊗ K)) W :=
  (diagramMappingSource W).mapIso
    (Iso.op (discrete.mapIso (β_ L K)))

private theorem braidMappingIso_hom (K L : SSet.{0}) (W : Space) :
    (braidMappingIso K L W).hom =
      diagramMappingPrecomp (discrete.map (β_ L K).hom) W := rfl

/-- Braiding commutes with every map in the unswitched parameter. -/
theorem braidMappingIso_natural {K L : SSet.{0}} (f : K ⟶ L)
    (N : SSet.{0}) (W : Space) :
    diagramMappingPrecomp (discrete.map (f ▷ N)) W ≫
        (braidMappingIso K N W).hom =
      (braidMappingIso L N W).hom ≫
        diagramMappingPrecomp (discrete.map (N ◁ f)) W := by
  rw [braidMappingIso_hom, braidMappingIso_hom,
    ← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp, ← discrete.map_comp]
  exact congrArg (fun g ↦ diagramMappingPrecomp (discrete.map g) W)
    (BraidedCategory.braiding_naturality_right N f).symm

/-- The literal `n`th row of the original horizontal cotensor is the
mapping space from `K` into the cotensor by the same `Δ[n]`. -/
def rowSwitchIso (K : SSet.{0}) (W : Space) (n : SimplexCategory) :
    (cotensor K W).obj (op n) ≅
      diagramMappingSpace (discrete.obj K)
        (cotensor (SSet.stdSimplex.obj n) W) :=
  braidMappingIso K (SSet.stdSimplex.obj n) W ≪≫
    (OrdinarySegalCotensorMappingIso.mappingIso
      (SSet.stdSimplex.obj n) K W).symm

/-- The switch intertwines the original cotensor parameter restriction
and strict precomposition from the same horizontal source map. -/
theorem rowSwitchIso_natural {K L : SSet.{0}} (f : K ⟶ L)
    (W : Space) (n : SimplexCategory) :
    (pre f W).app (op n) ≫ (rowSwitchIso K W n).hom =
      (rowSwitchIso L W n).hom ≫
        diagramMappingPrecomp (discrete.map f)
          (cotensor (SSet.stdSimplex.obj n) W) := by
  let F (A : SSet.{0}) :=
    OrdinarySegalCotensorMappingIso.mappingIso (SSet.stdSimplex.obj n) A W
  have hF : (F L).inv ≫
      diagramMappingPrecomp (discrete.map f)
        (cotensor (SSet.stdSimplex.obj n) W) ≫ (F K).hom =
      diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.obj n ◁ f)) W := by
    dsimp only [F]
    rw [OrdinarySegalCotensorMappingIso.mappingIso_natural_source,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply (cancel_mono (F K).hom).mp
  calc
    ((pre f W).app (op n) ≫ (rowSwitchIso K W n).hom) ≫ (F K).hom =
        diagramMappingPrecomp
            (discrete.map (f ▷ SSet.stdSimplex.obj n)) W ≫
          (braidMappingIso K (SSet.stdSimplex.obj n) W).hom := by
            dsimp only [rowSwitchIso, F]
            simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
              Iso.inv_hom_id, Category.comp_id]
            rw [OrdinarySegalHorizontalCotensor.pre_app]
    _ = (braidMappingIso L (SSet.stdSimplex.obj n) W).hom ≫
          diagramMappingPrecomp
            (discrete.map (SSet.stdSimplex.obj n ◁ f)) W :=
          braidMappingIso_natural f (SSet.stdSimplex.obj n) W
    _ = ((rowSwitchIso L W n).hom ≫
          diagramMappingPrecomp (discrete.map f)
            (cotensor (SSet.stdSimplex.obj n) W)) ≫ (F K).hom := by
          rw [rowSwitchIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
            Category.assoc, hF]

/-- The original parameter unit gives a map of the two literal cotensor
rows, with no replacement of its directed edge. -/
def unitRowArrowIso (W : Space) (n : SimplexCategory) :
    Arrow.mk ((pre (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W).app (op n)) ≅
      Arrow.mk (OrdinarySegalWalkingEvaluation.edgeEvaluation
        (cotensor (SSet.stdSimplex.obj n) W)) :=
  Arrow.isoMk
    (rowSwitchIso (GroupoidSimplex.parameter.obj ⦋1⦌) W n)
    ((rowSwitchIso (Δ[1] : SSet.{0}) W n) ≪≫
      OrdinarySegalWalkingEvaluation.simplexMappingIso
        (cotensor (SSet.stdSimplex.obj n) W) 1)
    (by
      change _ = (pre (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W).app (op n) ≫
        ((rowSwitchIso (Δ[1] : SSet.{0}) W n).hom ≫
          (OrdinarySegalWalkingEvaluation.simplexMappingIso
            (cotensor (SSet.stdSimplex.obj n) W) 1).hom)
      rw [← Category.assoc, rowSwitchIso_natural]
      rfl)

#print axioms braidMappingIso
#print axioms braidMappingIso_natural
#print axioms rowSwitchIso
#print axioms rowSwitchIso_natural
#print axioms unitRowArrowIso

end
end DaggerModels.PartII.OrdinarySegalCotensorRowSwitch
