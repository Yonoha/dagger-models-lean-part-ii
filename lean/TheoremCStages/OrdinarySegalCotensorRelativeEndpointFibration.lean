import OrdinarySegalCotensorEndpointCalibration
import OrdinarySegalCotensorSimplexCalibration
import OrdinarySegalOrderedMappingFibres

/-!
# The literal relative endpoint fibration of a horizontal cotensor

The source is the degree-one row of the unchanged cotensor. The target is
the pullback of its ordered endpoint map along the two copies of the
parameter restriction. The checked mapping corner supplies the fibration;
the isomorphism below retains both pullback legs and their order.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorRelativeEndpointFibration

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev boundary := (SSet.boundary 1).toSSet
private abbrev i := (SSet.boundary 1).ι
private abbrev ep (K : SSet.{0}) (W : Space) :=
  OrdinarySegalOrderedMappingFibres.endpointArrow (cotensor K W)
private abbrev epMap {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :=
  prod.map ((pre f W).app (op ⦋0⦌)) ((pre f W).app (op ⦋0⦌))
private abbrev B (K : SSet.{0}) (W : Space) :=
  OrdinarySegalCotensorEndpointCalibration.boundaryEndpointIso K W
private abbrev S (K : SSet.{0}) (W : Space) :=
  Iso.refl ((cotensor K W).obj (op ⦋1⦌))

/-- Naturality of the two actual faces, in ordered `(d₁,d₀)` order. -/
private theorem endpoint_natural {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    (pre f W).app (op ⦋1⦌) ≫ ep K W = ep L W ≫ epMap f W := by
  apply prod.hom_ext
  · rw [Category.assoc, OrdinarySegalOrderedMappingFibres.endpointArrow_fst,
      Category.assoc, prod.map_fst, ← Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointArrow_fst]
    exact ((pre f W).naturality (SimplexCategory.δ (1 : Fin 2)).op).symm
  · rw [Category.assoc, OrdinarySegalOrderedMappingFibres.endpointArrow_snd,
      Category.assoc, prod.map_snd, ← Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointArrow_snd]
    exact ((pre f W).naturality (SimplexCategory.δ (0 : Fin 2)).op).symm

/-- The literal relative ordered-endpoint comparison. -/
def relativeEndpoint {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    (cotensor L W).obj (op ⦋1⦌) ⟶
      pullback (ep K W) (epMap f W) :=
  pullback.lift ((pre f W).app (op ⦋1⦌)) (ep L W) (endpoint_natural f W)

private theorem boundary_source_fst (W : Space) :
    (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom ≫ prod.fst =
      diagramMappingPrecomp (discrete.map SSet.boundary₁.ι₀) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom := by
  simp only [OrdinarySegalCotensorBoundaryOne.endpointTargetIso,
    Iso.trans_hom, Category.assoc, prod.mapIso_hom, prod.map_fst]
  rw [← Category.assoc,
    OrdinarySegalCotensorBoundaryOne.boundaryMappingIso_fst]
  rfl

private theorem boundary_source_snd (W : Space) :
    (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom ≫ prod.snd =
      diagramMappingPrecomp (discrete.map SSet.boundary₁.ι₁) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom := by
  simp only [OrdinarySegalCotensorBoundaryOne.endpointTargetIso,
    Iso.trans_hom, Category.assoc, prod.mapIso_hom, prod.map_snd]
  rw [← Category.assoc,
    OrdinarySegalCotensorBoundaryOne.boundaryMappingIso_snd]
  rfl

private theorem simplex_boundary_faces (W : Space) :
    diagramMappingPrecomp (discrete.map i) W ≫
        (OrdinarySegalCotensorBoundaryOne.endpointTargetIso W).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom ≫
        OrdinarySegalOrderedMappingFibres.endpointArrow W := by
  apply prod.hom_ext
  · rw [Category.assoc, boundary_source_fst, Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointArrow_fst]
    rw [← Category.assoc, ← diagramMappingPrecomp_comp,
      ← discrete.map_comp, SSet.boundary₁.ι₀_ι]
    exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
      (SimplexCategory.δ (1 : Fin 2))
  · rw [Category.assoc, boundary_source_snd, Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointArrow_snd]
    rw [← Category.assoc, ← diagramMappingPrecomp_comp,
      ← discrete.map_comp, SSet.boundary₁.ι₁_ι]
    exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
      (SimplexCategory.δ (0 : Fin 2))

/-- Fubini carries the original boundary restriction to the actual pair
of ordered horizontal face maps. -/
private theorem boundary_face (K : SSet.{0}) (W : Space) :
    diagramMappingPrecomp (discrete.map (K ◁ i)) W ≫ (B K W).hom =
      ep K W := by
  let D := OrdinarySegalWalkingEvaluation.simplexMappingIso (cotensor K W) 1
  let F := OrdinarySegalCotensorMappingIso.mappingIso K boundary W
  let E := OrdinarySegalCotensorBoundaryOne.endpointTargetIso (cotensor K W)
  let A := diagramMappingPrecomp (discrete.map (K ◁ i)) W
  have h := OrdinarySegalCotensorMappingIso.mappingIso_natural_source K i W
  rw [OrdinarySegalCotensorSimplexCalibration.mappingIso_simplex_hom] at h
  have hD : diagramMappingPrecomp (discrete.map i) (cotensor K W) ≫ E.hom =
      D.hom ≫ ep K W := simplex_boundary_faces (cotensor K W)
  change A ≫ F.inv ≫ E.hom = ep K W
  apply (cancel_epi D.hom).mp
  calc
    D.hom ≫ (A ≫ F.inv ≫ E.hom) =
        (D.hom ≫ A) ≫ F.inv ≫ E.hom := by simp only [Category.assoc]
    _ = (diagramMappingPrecomp (discrete.map i) (cotensor K W) ≫ F.hom) ≫
          F.inv ≫ E.hom := by rw [h]
    _ = diagramMappingPrecomp (discrete.map i) (cotensor K W) ≫ E.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = D.hom ≫ ep K W := hD

private theorem boundary_parameter {K L : SSet.{0}} (f : K ⟶ L)
    (W : Space) :
    diagramMappingPrecomp (discrete.map (f ▷ boundary)) W ≫ (B K W).hom =
      (B L W).hom ≫ epMap f W :=
  OrdinarySegalCotensorEndpointCalibration.boundaryEndpointIso_natural f W

/-- The target of the checked corner is exactly the literal relative
ordered-endpoint pullback, with its two legs interchanged once. -/
def targetIso {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    pullback
        (diagramMappingPrecomp (discrete.map (f ▷ boundary)) W)
        (diagramMappingPrecomp (discrete.map (K ◁ i)) W) ≅
      pullback (ep K W) (epMap f W) :=
  pullbackSymmetry _ _ ≪≫
    asIso (pullback.map
      (diagramMappingPrecomp (discrete.map (K ◁ i)) W)
      (diagramMappingPrecomp (discrete.map (f ▷ boundary)) W)
      (ep K W) (epMap f W)
      (S K W).hom (B L W).hom (B K W).hom
      (boundary_face K W) (boundary_parameter f W))

private theorem targetIso_fst {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    (targetIso f W).hom ≫ pullback.fst (ep K W) (epMap f W) =
      pullback.snd
        (diagramMappingPrecomp (discrete.map (f ▷ boundary)) W)
        (diagramMappingPrecomp (discrete.map (K ◁ i)) W) ≫ (S K W).hom := by
  dsimp only [targetIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
    pullbackSymmetry_hom_comp_fst]

private theorem targetIso_snd {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    (targetIso f W).hom ≫ pullback.snd (ep K W) (epMap f W) =
      pullback.fst
        (diagramMappingPrecomp (discrete.map (f ▷ boundary)) W)
        (diagramMappingPrecomp (discrete.map (K ◁ i)) W) ≫ (B L W).hom := by
  dsimp only [targetIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
    pullbackSymmetry_hom_comp_snd]

/-- Exact arrow isomorphism, including the two legs of the relative
ordered-endpoint pullback. -/
def relativeEndpointArrowIso {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    Arrow.mk (OrdinarySegalCotensorEndpointCorner.corner f W) ≅
      Arrow.mk (relativeEndpoint f W) := by
  refine Arrow.isoMk (S L W) (targetIso f W) ?_
  change (S L W).hom ≫ relativeEndpoint f W =
    OrdinarySegalCotensorEndpointCorner.corner f W ≫ (targetIso f W).hom
  symm
  apply pullback.hom_ext
  · rw [Category.assoc, targetIso_fst, ← Category.assoc]
    rw [OrdinarySegalCotensorEndpointCorner.corner, pullback.lift_snd]
    rw [Category.assoc, relativeEndpoint, pullback.lift_fst]
    rfl
  · rw [Category.assoc, targetIso_snd, ← Category.assoc]
    rw [OrdinarySegalCotensorEndpointCorner.corner, pullback.lift_fst]
    rw [Category.assoc, relativeEndpoint, pullback.lift_snd]
    exact boundary_face L W

/-- The literal relative ordered-endpoint comparison is a Kan fibration. -/
theorem relativeEndpoint_fibration {K L : SSet.{0}} (f : K ⟶ L)
    [Mono f] (W : Space) [IsFibrant W] :
    Fibration (relativeEndpoint f W) := by
  apply (fibration_iff _).mpr
  exact ((fibrations SSet.{0}).arrow_mk_iso_iff
    (relativeEndpointArrowIso f W)).mp
      ((fibration_iff _).mp
        (OrdinarySegalCotensorEndpointCorner.corner_fibration f W))

#print axioms relativeEndpoint
#print axioms targetIso
#print axioms relativeEndpointArrowIso
#print axioms relativeEndpoint_fibration

end
end DaggerModels.PartII.OrdinarySegalCotensorRelativeEndpointFibration
