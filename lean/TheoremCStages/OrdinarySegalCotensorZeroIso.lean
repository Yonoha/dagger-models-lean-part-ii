import OrdinarySegalHorizontalCotensorPoint

/-!
# The original row-zero cotensor mapping isomorphism

The standard zero-simplex right unitor removes the literal final parameter
factor. The actual constant section is calibrated against the original
representable row-zero map and the unique parameter map to that simplex.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalCotensorZeroIso

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalWalkingEvaluation (simplexMappingIso)

noncomputable section

/-- The literal cotensor row zero is the original parameter mapping space. -/
def mappingIso (K : SSet.{0}) (W : Space) :
    (cotensor K W).obj (op ⦋0⦌) ≅ diagramMappingSpace (discrete.obj K) W :=
  (diagramMappingSource W).mapIso
    (Iso.op ((discrete.mapIso (SSet.stdSimplex.rightUnitor K)).symm))

theorem mappingIso_hom (K : SSet.{0}) (W : Space) :
    (mappingIso K W).hom =
      diagramMappingPrecomp (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W := rfl

/-- The actual row-zero constant section becomes the original constant
parameter map under the literal row-zero isomorphism. -/
theorem constantSection_mappingIso (K : SSet.{0}) (W : Space) :
    (constantSection K W).app (op ⦋0⦌) ≫ (mappingIso K W).hom =
      (simplexMappingIso W 0).inv ≫
        diagramMappingPrecomp (discrete.map (SSet.stdSimplex.isTerminalObj₀.from K)) W := by
  let t := SSet.stdSimplex.isTerminalObj₀.from K
  let u := (SSet.stdSimplex.rightUnitor K).inv ≫
    (t ▷ (Δ[0] : SSet.{0})) ≫ (SSet.stdSimplex.leftUnitor (Δ[0] : SSet.{0})).hom
  have hu : u = t := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  change ((simplexMappingIso W 0).inv ≫
      diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.leftUnitor (Δ[0] : SSet.{0})).hom) W) ≫
      diagramMappingPrecomp (discrete.map (t ▷ (Δ[0] : SSet.{0}))) W ≫
      diagramMappingPrecomp (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W = _
  calc
    _ = (simplexMappingIso W 0).inv ≫
        diagramMappingPrecomp (discrete.map u) W := by
      dsimp only [u]
      simp only [discrete.map_comp, diagramMappingPrecomp_comp, Category.assoc]
    _ = _ := by rw [hu]

#print axioms mappingIso
#print axioms constantSection_mappingIso

end
end DaggerModels.PartII.OrdinarySegalCotensorZeroIso
