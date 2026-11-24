import OrdinarySegalHorizontalCotensorPoint
import DaggerModelsPartII.DiagramMappingPushout
import TopCatModelCategory.SSet.Square

/-!
# The two triangles of the ordinary interval square

The pinned square pushout has two standard two-simplices sharing their middle
face. Horizontal discretization and the diagram mapping functor identify maps
out of the literal interval square with the pullback of its two triangle rows.
Every object and face below is an original ordinary simplicial-space row.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinaryIntervalPrismMappingIso

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalWalkingEvaluation (simplexMappingIso simplexMappingIso_natural)

noncomputable section

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan
      (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
      (SimplicialObject.const (Type 0)))
  infer_instance

private abbrev square := (Δ[1] ⊗ Δ[1] : SSet.{0})
private abbrev squareMapping (W : Space) := diagramMappingSpace (discrete.obj square) W
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private def middleFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op

/-- Restriction to the triangle with vertices `(0,0),(1,0),(1,1)`. -/
def lower (W : Space) : squareMapping W ⟶ row W 2 :=
  diagramMappingPrecomp (discrete.map SSet.square.ιTriangle₀) W ≫
    (simplexMappingIso W 2).hom

/-- Restriction to the triangle with vertices `(0,0),(0,1),(1,1)`. -/
def upper (W : Space) : squareMapping W ⟶ row W 2 :=
  diagramMappingPrecomp (discrete.map SSet.square.ιTriangle₁) W ≫
    (simplexMappingIso W 2).hom

/-- The literal pinned square pushout remains a pushout after horizontal
discretization. -/
def discreteSquarePushout : IsPushout
    (discrete.map (SSet.stdSimplex.δ (1 : Fin 3)))
    (discrete.map (SSet.stdSimplex.δ (1 : Fin 3)))
    (discrete.map SSet.square.ιTriangle₀)
    (discrete.map SSet.square.ιTriangle₁) :=
  SSet.square.isPushout.map discrete

/-- Mapping out of the square is a strict pullback before row calibration. -/
def squareMappingPullback (W : Space) : IsPullback
    (diagramMappingPrecomp (discrete.map SSet.square.ιTriangle₀) W)
    (diagramMappingPrecomp (discrete.map SSet.square.ιTriangle₁) W)
    (diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (1 : Fin 3))) W)
    (diagramMappingPrecomp
      (discrete.map (SSet.stdSimplex.δ (1 : Fin 3))) W) :=
  diagramMappingSpace_isPullback discreteSquarePushout W

/-- Under the same representable row isomorphism, both middle-face maps
are the original `d₁ : W₂ ⟶ W₁`. -/
def rowSquarePullback (W : Space) :
    IsPullback (lower W) (upper W) (middleFace W) (middleFace W) := by
  apply (squareMappingPullback W).of_iso
    (Iso.refl (squareMapping W))
    (simplexMappingIso W 2) (simplexMappingIso W 2)
    (simplexMappingIso W 1)
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · exact simplexMappingIso_natural W (SimplexCategory.δ (1 : Fin 3))
  · exact simplexMappingIso_natural W (SimplexCategory.δ (1 : Fin 3))

/-- The literal interval-square mapping space is exactly the strict
pullback of the two original row-two middle faces. -/
def mappingIso (W : Space) :
    squareMapping W ≅ pullback (middleFace W) (middleFace W) :=
  (rowSquarePullback W).isoPullback

theorem mappingIso_lower (W : Space) :
    (mappingIso W).hom ≫ pullback.fst (middleFace W) (middleFace W) = lower W :=
  (rowSquarePullback W).isoPullback_hom_fst

theorem mappingIso_upper (W : Space) :
    (mappingIso W).hom ≫ pullback.snd (middleFace W) (middleFace W) = upper W :=
  (rowSquarePullback W).isoPullback_hom_snd

/-- The row-zero interval cotensor is the original row of edges. -/
def intervalZeroIso (W : Space) :
    (OrdinarySegalHorizontalCotensor.cotensor (Δ[1] : SSet.{0}) W).obj
        (op ⦋0⦌) ≅ row W 1 :=
  (diagramMappingSource W).mapIso
      (Iso.op ((discrete.mapIso
        (SSet.stdSimplex.rightUnitor (Δ[1] : SSet.{0}))).symm)) ≪≫
    simplexMappingIso W 1

private theorem intervalZeroIso_hom (W : Space) :
    (intervalZeroIso W).hom =
      diagramMappingPrecomp
          (discrete.map
            (SSet.stdSimplex.rightUnitor (Δ[1] : SSet.{0})).inv) W ≫
        (simplexMappingIso W 1).hom := rfl

/-- The lower triangle's bottom edge is the original `d₂` face. -/
theorem lower_bottom (W : Space) :
    lower W ≫ W.map (SimplexCategory.δ (Fin.last 2)).op =
      diagramMappingPrecomp (discrete.map (SSet.ι₀ : (Δ[1] : SSet.{0}) ⟶ square)) W ≫
        (simplexMappingIso W 1).hom := by
  dsimp only [lower]
  rw [Category.assoc, ← simplexMappingIso_natural W
    (SimplexCategory.δ (Fin.last 2))]
  rw [← Category.assoc, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp]
  change diagramMappingPrecomp (discrete.map
    (SSet.stdSimplex.δ (2 : Fin 3) ≫ SSet.square.ιTriangle₀)) W ≫
      (simplexMappingIso W 1).hom = _
  rw [SSet.square.δ₂_ιTriangle₀]

/-- The upper triangle's top edge is the original `d₀` face. -/
theorem upper_top (W : Space) :
    upper W ≫ W.map (SimplexCategory.δ (0 : Fin 3)).op =
      diagramMappingPrecomp (discrete.map (SSet.ι₁ : (Δ[1] : SSet.{0}) ⟶ square)) W ≫
        (simplexMappingIso W 1).hom := by
  dsimp only [upper]
  rw [Category.assoc, ← simplexMappingIso_natural W
    (SimplexCategory.δ (0 : Fin 3))]
  rw [← Category.assoc, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp]
  change diagramMappingPrecomp (discrete.map
    (SSet.stdSimplex.δ (0 : Fin 3) ≫ SSet.square.ιTriangle₁)) W ≫
      (simplexMappingIso W 1).hom = _
  rw [SSet.square.δ₀_ιTriangle₁]

/-- The row source face in the interval cotensor is exactly the lower
horizontal edge of the literal square. -/
theorem interval_source_endpoint (W : Space) :
    (OrdinarySegalHorizontalCotensor.cotensor (Δ[1] : SSet.{0}) W).map
        (SimplexCategory.δ (1 : Fin 2)).op ≫ (intervalZeroIso W).hom =
      lower W ≫ W.map (SimplexCategory.δ (Fin.last 2)).op := by
  rw [OrdinarySegalHorizontalCotensor.cotensor_map, intervalZeroIso_hom]
  rw [← Category.assoc, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp]
  change diagramMappingPrecomp (discrete.map
    ((SSet.stdSimplex.rightUnitor (Δ[1] : SSet)).inv ≫
      (Δ[1] : SSet) ◁ SSet.stdSimplex.δ (1 : Fin 2))) W ≫
        (simplexMappingIso W 1).hom = _
  rw [SSet.stdSimplex.rightUnitor_inv_map_δ_one]
  exact (lower_bottom W).symm

/-- The row target face in the interval cotensor is exactly the upper
horizontal edge of the literal square. -/
theorem interval_target_endpoint (W : Space) :
    (OrdinarySegalHorizontalCotensor.cotensor (Δ[1] : SSet.{0}) W).map
        (SimplexCategory.δ (0 : Fin 2)).op ≫ (intervalZeroIso W).hom =
      upper W ≫ W.map (SimplexCategory.δ (0 : Fin 3)).op := by
  rw [OrdinarySegalHorizontalCotensor.cotensor_map, intervalZeroIso_hom]
  rw [← Category.assoc, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp]
  change diagramMappingPrecomp (discrete.map
    ((SSet.stdSimplex.rightUnitor (Δ[1] : SSet)).inv ≫
      (Δ[1] : SSet) ◁ SSet.stdSimplex.δ (0 : Fin 2))) W ≫
        (simplexMappingIso W 1).hom = _
  rw [SSet.stdSimplex.rightUnitor_inv_map_δ_zero]
  exact (upper_top W).symm

#print axioms discreteSquarePushout
#print axioms squareMappingPullback
#print axioms rowSquarePullback
#print axioms mappingIso
#print axioms mappingIso_lower
#print axioms mappingIso_upper
#print axioms intervalZeroIso
#print axioms interval_source_endpoint
#print axioms interval_target_endpoint

end

end DaggerModels.PartII.OrdinaryIntervalPrismMappingIso
