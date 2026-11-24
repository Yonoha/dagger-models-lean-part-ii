import DaggerModelsPartII.JTCylinderStaircaseFaces
import DaggerModelsPartII.JTCylinderFrame
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Ordered endpoint section of the reduced standard cylinder

The ordered boundary has a representative in the uncollapsed prism that
uses its first and last prism vertices. The reduced-cylinder projection
is an epimorphism because the boundary-cylinder projection has this
explicit section. Its coordinate factorization places the representative
in every maximal staircase cell, and the quotient images cover the
reduced cylinder.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial

namespace DaggerModels.PartII.JTCylinderQuotientImages

open JTXiEndpointCollapse JTCylinderStaircase
open JTCylinderStaircaseFaces

noncomputable section

/-- On the two ordered boundary vertices, choose respectively the first
and the last parameter vertex. -/
def parameterOnBoundary (k : ℕ) : boundary ⟶ (Δ[k] : SSet.{0}) :=
  JTCylinderFrame.j ≫ SSet.stdSimplex.map (SimplexCategory.diag k)

/-- A section of the boundary-cylinder projection that spans the two
extreme vertices of the uncollapsed prism. -/
def endpointPair (k : ℕ) : boundary ⟶ boundary ⊗ (Δ[k] : SSet.{0}) :=
  CartesianMonoidalCategory.lift (𝟙 boundary) (parameterOnBoundary k)

/-- The common ordered endpoint representative in the uncollapsed prism. -/
def endpointRepresentative (k : ℕ) :
    boundary ⟶ interval ⊗ (Δ[k] : SSet.{0}) :=
  endpointPair k ≫
    (ReducedCylinder.tensorInclusion JTCylinderFrame.j).app (Δ[k] : SSet.{0})

private instance boundaryProjection_splitEpi (k : ℕ) :
    IsSplitEpi ((ReducedCylinder.tensorProjection boundary).app (Δ[k] : SSet.{0})) :=
  IsSplitEpi.mk' {
    section_ := endpointPair k
    id := by
      change endpointPair k ≫
        CartesianMonoidalCategory.fst boundary (Δ[k] : SSet.{0}) = 𝟙 boundary
      exact CartesianMonoidalCategory.lift_fst _ _ }

/-- The actual quotient map from the uncollapsed prism is epic in every
standard-simplex degree. -/
instance cylinder_epi (k : ℕ) : Epi (JTCylinderFrame.cylinder ⦋k⦌) := by
  haveI : Epi ((ReducedCylinder.tensorProjection boundary).app (Δ[k] : SSet.{0})) :=
    inferInstance
  exact PushoutCocone.epi_inl_of_is_pushout_of_epi
    (JTCylinderFrame.isPushout ⦋k⦌).isColimit

/-- The chosen common representative descends to the literal ordered
boundary map of the reduced cylinder. -/
theorem endpointRepresentative_quotient (k : ℕ) :
    endpointRepresentative k ≫ JTCylinderFrame.cylinder ⦋k⦌ =
      JTCylinderFrame.boundary.app ⦋k⦌ := by
  have hw := (JTCylinderFrame.isPushout ⦋k⦌).w
  change
    (ReducedCylinder.tensorInclusion JTCylinderFrame.j).app (Δ[k] : SSet.{0}) ≫
      JTCylinderFrame.cylinder ⦋k⦌ =
    (ReducedCylinder.tensorProjection boundary).app (Δ[k] : SSet.{0}) ≫
      JTCylinderFrame.boundary.app ⦋k⦌ at hw
  calc
    endpointRepresentative k ≫ JTCylinderFrame.cylinder ⦋k⦌ =
      endpointPair k ≫
        ((ReducedCylinder.tensorInclusion JTCylinderFrame.j).app
          (Δ[k] : SSet.{0}) ≫ JTCylinderFrame.cylinder ⦋k⦌) := by
        simp only [endpointRepresentative, Category.assoc]
    _ = endpointPair k ≫
        ((ReducedCylinder.tensorProjection boundary).app (Δ[k] : SSet.{0}) ≫
          JTCylinderFrame.boundary.app ⦋k⦌) := congrArg (fun f ↦ endpointPair k ≫ f) hw
    _ = JTCylinderFrame.boundary.app ⦋k⦌ := by
        rw [← Category.assoc]
        change (endpointPair k ≫
          CartesianMonoidalCategory.fst boundary (Δ[k] : SSet.{0})) ≫
            JTCylinderFrame.boundary.app ⦋k⦌ = _
        simp only [endpointPair, CartesianMonoidalCategory.lift_fst,
          Category.id_comp]

/-- The width coordinate of a specified maximal prism simplex. -/
private def staircaseWidthHom (k : ℕ) (t : Fin (k + 1)) :
    ⦋k + 1⦌ ⟶ ⦋k⦌ :=
  SimplexCategory.Hom.mk (OrderHom.snd.comp (staircaseOrder k t))

private theorem staircaseSimplex_snd (k : ℕ) (t : Fin (k + 1)) :
    staircaseSimplex k t ≫
        CartesianMonoidalCategory.snd (Δ[1] : SSet.{0}) Δ[k] =
      SSet.stdSimplex.map (staircaseWidthHom k t) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  rfl

/-- The long diagonal crosses the cut once. -/
private theorem diag_cut (k : ℕ) (t : Fin (k + 1)) :
    SimplexCategory.diag (k + 1) ≫ cutHom k t = 𝟙 ⦋1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  fin_cases i
  · simp [SimplexCategory.diag, SimplexCategory.mkOfLe,
      cutHom, staircaseOrder, SimplexCategory.comp_toOrderHom]
  · have ht : ¬ k < t.val := by omega
    simp [SimplexCategory.diag, SimplexCategory.mkOfLe,
      cutHom, staircaseOrder, SimplexCategory.comp_toOrderHom, ht]

/-- The same diagonal begins at parameter vertex zero and ends at `k`. -/
private theorem diag_width (k : ℕ) (t : Fin (k + 1)) :
    SimplexCategory.diag (k + 1) ≫ staircaseWidthHom k t =
      SimplexCategory.diag k := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  fin_cases i
  · simp [SimplexCategory.diag, SimplexCategory.mkOfLe,
      staircaseWidthHom, staircaseOrder, SimplexCategory.comp_toOrderHom]
  · have ht : ¬ k < t.val := by omega
    simp [SimplexCategory.diag, SimplexCategory.mkOfLe,
      staircaseWidthHom, staircaseOrder, SimplexCategory.comp_toOrderHom, ht]

private theorem endpointRepresentative_fst (k : ℕ) :
    endpointRepresentative k ≫
        CartesianMonoidalCategory.fst interval (Δ[k] : SSet.{0}) =
      JTCylinderFrame.j := by
  change (endpointPair k ≫ (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[k] : SSet.{0}))) ≫
      CartesianMonoidalCategory.fst interval (Δ[k] : SSet.{0}) = _
  rw [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
    ← Category.assoc]
  simp only [endpointPair, CartesianMonoidalCategory.lift_fst, Category.id_comp]

private theorem endpointRepresentative_snd (k : ℕ) :
    endpointRepresentative k ≫
        CartesianMonoidalCategory.snd interval (Δ[k] : SSet.{0}) =
      parameterOnBoundary k := by
  change (endpointPair k ≫ (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[k] : SSet.{0}))) ≫
      CartesianMonoidalCategory.snd interval (Δ[k] : SSet.{0}) = _
  rw [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
    ← Category.assoc]
  simp only [endpointPair, CartesianMonoidalCategory.lift_snd, Category.comp_id]

/-- The chosen endpoint representative factors through every specified
maximal staircase simplex, not through an assumed quotient cell. -/
theorem endpointRepresentative_factors (k : ℕ) (t : Fin (k + 1)) :
    endpointRepresentative k =
      (JTCylinderFrame.j ≫
        SSet.stdSimplex.map (SimplexCategory.diag (k + 1))) ≫
          staircaseSimplex k t := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [endpointRepresentative_fst]
    dsimp only [JTXiEndpointCollapse.interval]
    rw [Category.assoc, staircaseSimplex_fst]
    rw [Category.assoc, ← SSet.stdSimplex.map_comp, diag_cut,
      CategoryTheory.Functor.map_id,
      Category.comp_id]
  · rw [endpointRepresentative_snd]
    dsimp only [JTXiEndpointCollapse.interval]
    rw [Category.assoc, staircaseSimplex_snd]
    rw [Category.assoc, ← SSet.stdSimplex.map_comp, diag_width]
    rfl

/-- The common endpoint representative lies in each uncollapsed maximal
prism cell, including both extreme cuts. -/
theorem endpointRepresentative_range_le (k : ℕ) (t : Fin (k + 1)) :
    SSet.Subcomplex.range (endpointRepresentative k) ≤ staircaseImage k t := by
  rw [endpointRepresentative_factors]
  change SSet.Subcomplex.range
      ((JTCylinderFrame.j ≫
        SSet.stdSimplex.map (SimplexCategory.diag (k + 1))) ≫
          staircaseSimplex k t) ≤
      SSet.Subcomplex.ofSimplex (SSet.yonedaEquiv (staircaseSimplex k t))
  rw [← SSet.Subcomplex.range_eq_ofSimplex]
  exact Subfunctor.range_comp_le _ _

/-- The image of a specified maximal prism cell in the actual reduced
cylinder, with the original quotient map. -/
def quotientImage (k : ℕ) (t : Fin (k + 1)) :
    (JTCylinderFrame.value.obj ⦋k⦌).Subcomplex :=
  (staircaseImage k t).image (JTCylinderFrame.cylinder ⦋k⦌)

/-- The maximal prism cells cover the actual reduced cylinder, including
the one-cell case `k=0`. -/
theorem quotient_cover (k : ℕ) :
    (⨆ t : Fin (k + 1), quotientImage k t) = ⊤ := by
  change (⨆ t : Fin (k + 1),
    (staircaseImage k t).image (JTCylinderFrame.cylinder ⦋k⦌)) = ⊤
  rw [← SSet.Subcomplex.image_iSup, staircase_cover,
    SSet.Subcomplex.image_top, SSet.Subcomplex.range_eq_top]

end

end DaggerModels.PartII.JTCylinderQuotientImages
