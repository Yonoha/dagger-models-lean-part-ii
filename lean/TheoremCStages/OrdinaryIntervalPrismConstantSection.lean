import OrdinaryIntervalPrismMappingIso

/-!
# The actual constant interval section on the two square triangles

The constant section of the checked horizontal cotensor is evaluated in the
original row-one degree. Its two triangle restrictions are exactly the
original degeneracies `σ₀` and `σ₁`, in lower/upper order. This is a strict
identification, with no Segal or fibrancy assumption.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.OrdinaryIntervalPrismConstantSection

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryIntervalPrismMappingIso (lower upper mappingIso)
open OrdinarySegalWalkingEvaluation (simplexMappingIso simplexMappingIso_natural)
open OrdinarySegalHorizontalCotensorPoint (constantSection)

noncomputable section

private abbrev square := (Δ[1] ⊗ Δ[1] : SSet.{0})

/-- The lower triangle has second-coordinate word `(0,0,1)`. -/
theorem lower_second :
    SSet.square.ιTriangle₀ ≫ (snd _ _ : square ⟶ (Δ[1] : SSet.{0})) =
      SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  rw [← SSet.yonedaEquiv_snd, SSet.stdSimplex.yonedaEquiv_map]
  rfl

/-- The upper triangle has second-coordinate word `(0,1,1)`. -/
theorem upper_second :
    SSet.square.ιTriangle₁ ≫ (snd _ _ : square ⟶ (Δ[1] : SSet.{0})) =
      SSet.stdSimplex.map (SimplexCategory.σ (1 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  rw [← SSet.yonedaEquiv_snd, SSet.stdSimplex.yonedaEquiv_map]
  rfl

/-- The square mapping operation that is constant in its first interval
coordinate, expressed using the actual original row-one mapping iso. -/
def constantSquare (W : Space) :
    W.obj (op ⦋1⦌) ⟶
      diagramMappingSpace (discrete.obj square) W :=
  (simplexMappingIso W 1).inv ≫
    diagramMappingPrecomp (discrete.map (snd _ _ : square ⟶ (Δ[1] : SSet.{0}))) W

/-- Restricting the constant square to its lower triangle gives the
literal first degeneracy of an original one-simplex. -/
theorem constantSquare_lower (W : Space) :
    constantSquare W ≫ lower W =
      W.map (SimplexCategory.σ (0 : Fin 2)).op := by
  calc
    constantSquare W ≫ lower W =
        (simplexMappingIso W 1).inv ≫
          (diagramMappingPrecomp
              (discrete.map (SSet.square.ιTriangle₀ ≫
                (snd _ _ : square ⟶ (Δ[1] : SSet.{0})))) W ≫
            (simplexMappingIso W 2).hom) := by
      simp only [constantSquare, lower, discrete.map_comp,
        diagramMappingPrecomp_comp, Category.assoc]
    _ = (simplexMappingIso W 1).inv ≫
          (diagramMappingPrecomp
              (discrete.map (SSet.stdSimplex.map
                (SimplexCategory.σ (0 : Fin 2)))) W ≫
            (simplexMappingIso W 2).hom) := by rw [lower_second]
    _ = (simplexMappingIso W 1).inv ≫
          ((simplexMappingIso W 1).hom ≫
            W.map (SimplexCategory.σ (0 : Fin 2)).op) := by
      rw [simplexMappingIso_natural W (SimplexCategory.σ (0 : Fin 2))]
    _ = W.map (SimplexCategory.σ (0 : Fin 2)).op := by simp

/-- Restricting the constant square to its upper triangle gives the
literal second degeneracy of an original one-simplex. -/
theorem constantSquare_upper (W : Space) :
    constantSquare W ≫ upper W =
      W.map (SimplexCategory.σ (1 : Fin 2)).op := by
  calc
    constantSquare W ≫ upper W =
        (simplexMappingIso W 1).inv ≫
          (diagramMappingPrecomp
              (discrete.map (SSet.square.ιTriangle₁ ≫
                (snd _ _ : square ⟶ (Δ[1] : SSet.{0})))) W ≫
            (simplexMappingIso W 2).hom) := by
      simp only [constantSquare, upper, discrete.map_comp,
        diagramMappingPrecomp_comp, Category.assoc]
    _ = (simplexMappingIso W 1).inv ≫
          (diagramMappingPrecomp
              (discrete.map (SSet.stdSimplex.map
                (SimplexCategory.σ (1 : Fin 2)))) W ≫
            (simplexMappingIso W 2).hom) := by rw [upper_second]
    _ = (simplexMappingIso W 1).inv ≫
          ((simplexMappingIso W 1).hom ≫
            W.map (SimplexCategory.σ (1 : Fin 2)).op) := by
      rw [simplexMappingIso_natural W (SimplexCategory.σ (1 : Fin 2))]
    _ = W.map (SimplexCategory.σ (1 : Fin 2)).op := by simp

/-- The actual cotensor constant section, not a substitute map, is the
constant-first-coordinate square map at original row degree one. -/
theorem constantSection_app_one (W : Space) :
    (constantSection (Δ[1] : SSet.{0}) W).app (op ⦋1⦌) =
      constantSquare W := by
  change (simplexMappingIso W 1).inv ≫
      diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.leftUnitor (Δ[1] : SSet.{0})).hom) W ≫
      diagramMappingPrecomp
        (discrete.map
          (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0}) ▷
            (Δ[1] : SSet.{0}))) W =
    (simplexMappingIso W 1).inv ≫
      diagramMappingPrecomp
        (discrete.map (snd _ _ : square ⟶ (Δ[1] : SSet.{0}))) W
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp]
  change (simplexMappingIso W 1).inv ≫
      diagramMappingPrecomp
        (discrete.map
          ((SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0}) ▷
            (Δ[1] : SSet.{0})) ≫
            (snd _ _ : (Δ[0] ⊗ Δ[1] : SSet.{0}) ⟶ (Δ[1] : SSet.{0})))) W =
    constantSquare W
  rw [whiskerRight_snd]
  rfl

/-- The actual constant section maps to the lower `σ₀` and upper `σ₁`
two-simplex, without changing the original interval or row. -/
theorem constantSection_triangles (W : Space) :
    (constantSection (Δ[1] : SSet.{0}) W).app (op ⦋1⦌) ≫ lower W =
        W.map (SimplexCategory.σ (0 : Fin 2)).op ∧
      (constantSection (Δ[1] : SSet.{0}) W).app (op ⦋1⦌) ≫ upper W =
        W.map (SimplexCategory.σ (1 : Fin 2)).op := by
  rw [constantSection_app_one]
  exact ⟨constantSquare_lower W, constantSquare_upper W⟩

#print axioms lower_second
#print axioms upper_second
#print axioms constantSquare_lower
#print axioms constantSquare_upper
#print axioms constantSection_app_one
#print axioms constantSection_triangles

end

end DaggerModels.PartII.OrdinaryIntervalPrismConstantSection
