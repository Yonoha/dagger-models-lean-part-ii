import OrdinarySegalAllVertexDiagonal

/-!
# Coordinate calibration of the complete vertex diagonal

The comparison keeps every ordered vertex and the actual corrected unit.
Both triangles are statements about the original maps, without a fibrant
replacement or a selected endpoint pair.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

namespace DaggerModels.PartII.OrdinarySegalAllVertexDiagonalCalibration

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap)
open OrdinarySegalAllVertexDiagonal (vertexBaseDiagonalIso)

noncomputable section

private abbrev R (W : Space) := OrdinarySegalPrecompletion.resolution W
private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W

/-- The original complete vertex restriction has the same diagonal as the
actual full-tuple arrow of the outer resolution. -/
theorem vertexMap_diagonal (W : Space) (n : ℕ) :
    vertexMap (P W) n ≫ (vertexBaseDiagonalIso W n).hom =
      diagonalFunctor.map (OrdinarySegalAllVertexResolution.vertexResolution W n) := by
  let i := OrdinarySegalVertexTupleFibres.vertexInclusion n
  let H := DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso (P W) n
  let M := OrdinaryDiscreteMapping.mappingIso (Δ[n] : SSet.{0}) (P W)
  let T := OrdinaryDiscreteMapping.mappingIso (vertices n) (P W)
  let V := HorizontalMappingVerticalDiagonal.horizontalMappingDiagonalIso (vertices n) (R W)
  let D := diagonalFunctor.mapIso
    (OrdinarySegalAllVertexDiagonal.rowDiscreteMappingIso (vertices n) (R W))
  have hn := OrdinaryDiscreteMapping.mappingIso_natural i (P W)
  have h₁ : vertexMap (P W) n ≫ (vertexBaseDiagonalIso W n).hom =
      H.inv ≫ DaggerNativeBisimplicialHorizontalMapping.horizontalPre i (P W) ≫
        V.hom ≫ D.inv := by
    change H.inv ≫ M.inv ≫
      (DaggerModels.PartII.diagramMappingPrecomp (discrete.map i) (P W) ≫ T.hom) ≫
        V.hom ≫ D.inv = _
    rw [hn]
    dsimp only [M]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h₁]
  have hs := HorizontalMappingVerticalDiagonal.horizontalPre_triangle i (R W)
  have hs' := congrArg (fun k ↦ H.inv ≫ k ≫ D.inv) hs
  calc
    H.inv ≫ DaggerNativeBisimplicialHorizontalMapping.horizontalPre i (P W) ≫
        V.hom ≫ D.inv =
      H.inv ≫
        (HorizontalMappingVerticalDiagonal.horizontalMappingDiagonalIso
          (Δ[n] : SSet.{0}) (R W)).hom ≫
        diagonalFunctor.map ((R W).whiskerLeft
          (HorizontalMappingVerticalDiagonal.horizontalPreNatural i)) ≫ D.inv := by
            simpa only [Category.assoc] using hs'
    _ = diagonalFunctor.map (OrdinarySegalAllVertexResolution.vertexResolution W n) := by
      apply NatTrans.ext
      funext q x
      rfl

/-- Apply the original complete vertex mapping functor to the outer unit. -/
def vertexBaseUnit (W : Space) (n : ℕ) :
    (Functor.const SimplexCategoryᵒᵖ).obj
        (diagramMappingSpace (discrete.obj (vertices n)) W) ⟶
      OrdinarySegalAllVertexResolution.vertexBaseResolution W n :=
  Functor.whiskerRight (OrdinarySegalPrecompletion.resolutionUnit W)
    (diagramMappingTarget (discrete.obj (vertices n)))

/-- The original unit on the complete vertex-mapping base is its exact
outer unit followed by the corrected vertical diagonal. -/
theorem vertexBaseUnit_diagonal (W : Space) (n : ℕ) :
    diagramMappingPostcomp (discrete.obj (vertices n))
        (OrdinarySegalVerticalPrecompletion.unit W) ≫
      (vertexBaseDiagonalIso W n).hom =
    (OrdinarySegalVerticalPrecompletionFiberComparison.constantDiagonalIso
      (diagramMappingSpace (discrete.obj (vertices n)) W)).inv ≫
      diagonalFunctor.map (vertexBaseUnit W n) := by
  let M := OrdinaryDiscreteMapping.mappingIso (vertices n) W
  let V := HorizontalMappingVerticalDiagonal.horizontalMappingDiagonalIso (vertices n) (R W)
  let D := diagonalFunctor.mapIso
    (OrdinarySegalAllVertexDiagonal.rowDiscreteMappingIso (vertices n) (R W))
  have hn := OrdinarySegalRestrictionTargetNaturality.mappingIso_post
    (vertices n) (OrdinarySegalVerticalPrecompletion.unit W)
  have h₁ : diagramMappingPostcomp (discrete.obj (vertices n))
        (OrdinarySegalVerticalPrecompletion.unit W) ≫
        (vertexBaseDiagonalIso W n).hom =
      M.hom ≫ DaggerNativeBisimplicialHorizontalMapping.horizontalMap
        (vertices n) (OrdinarySegalVerticalPrecompletion.unit W) ≫ V.hom ≫ D.inv := by
    simpa only [vertexBaseDiagonalIso,
      HorizontalMappingVerticalDiagonal.diagramMappingDiagonalIso,
      Iso.trans_hom, Category.assoc] using
        congrArg (fun m ↦ m ≫ V.hom ≫ D.inv) hn
  rw [h₁]
  apply (cancel_mono D.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply NatTrans.ext
  funext q x
  apply NatTrans.ext
  funext m z
  rfl

#print axioms vertexMap_diagonal
#print axioms vertexBaseUnit_diagonal

end

end DaggerModels.PartII.OrdinarySegalAllVertexDiagonalCalibration
