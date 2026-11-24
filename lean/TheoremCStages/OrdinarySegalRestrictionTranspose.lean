import OrdinaryDiscreteMapping
import DaggerModelsPartII.DiagramRestrictionLimits
import DaggerModelsPartII.JTCylinderCEComparison

/-!
# Exact ordinary mapping and restriction transpose

The native horizontal mapping space from an ordinary discrete simplicial
set is the levelwise Hom simplicial set of the flipped original diagram.
The existing restriction-Hom equivalence therefore transposes a vertical
family of such maps into one map to the actual vertical limit restriction.
Both variable naturalities retain the same original parameters.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalRestrictionTranspose

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

/-- Maps from the actual ordinary discrete diagram transpose to maps into
the actual limit restriction, without fibrancy or Segal hypotheses. -/
def transpose (K A : SSet.{0}) (W : Space) :
    (K ⟶ diagramMappingSpace (discrete.obj A) W) ≃
      (A ⟶ diagramRestriction K W.flip) where
  toFun h := diagramRestrictionHomEquiv K A W.flip
    (h ≫ (OrdinaryDiscreteMapping.mappingIso A W).hom)
  invFun g := (diagramRestrictionHomEquiv K A W.flip).symm g ≫
    (OrdinaryDiscreteMapping.mappingIso A W).inv
  left_inv h := by
    dsimp
    rw [Equiv.symm_apply_apply, Category.assoc,
      (OrdinaryDiscreteMapping.mappingIso A W).hom_inv_id, Category.comp_id]
  right_inv g := by
    dsimp
    rw [Category.assoc, (OrdinaryDiscreteMapping.mappingIso A W).inv_hom_id]
    have h : (diagramRestrictionHomEquiv K A W.flip).symm g ≫
        𝟙 (diagramHomSSet A W.flip) = (diagramRestrictionHomEquiv K A W.flip).symm g :=
      Category.comp_id _
    exact (congrArg (diagramRestrictionHomEquiv K A W.flip) h).trans
      ((diagramRestrictionHomEquiv K A W.flip).apply_symm_apply g)

/-- Restriction in the vertical simplicial parameter commutes with transpose. -/
theorem transpose_pre {K L A : SSet.{0}} (v : K ⟶ L) (W : Space)
    (h : L ⟶ diagramMappingSpace (discrete.obj A) W) :
    transpose K A W (v ≫ h) =
      transpose L A W h ≫ diagramRestrictionPre v W.flip := by
  change diagramRestrictionHomEquiv K A W.flip
      ((v ≫ h) ≫ (OrdinaryDiscreteMapping.mappingIso A W).hom) =
    diagramRestrictionHomEquiv L A W.flip
      (h ≫ (OrdinaryDiscreteMapping.mappingIso A W).hom) ≫
        diagramRestrictionPre v W.flip
  rw [Category.assoc]
  exact diagramRestrictionHomEquiv_pre v
    (h ≫ (OrdinaryDiscreteMapping.mappingIso A W).hom)

/-- Horizontal precomposition commutes with transpose on the original map. -/
theorem transpose_coeff {K A B : SSet.{0}} (j : A ⟶ B) (W : Space)
    (h : K ⟶ diagramMappingSpace (discrete.obj B) W) :
    transpose K A W (h ≫ diagramMappingPrecomp (discrete.map j) W) =
      j ≫ transpose K B W h := by
  change diagramRestrictionHomEquiv K A W.flip
      ((h ≫ diagramMappingPrecomp (discrete.map j) W) ≫
        (OrdinaryDiscreteMapping.mappingIso A W).hom) =
    j ≫ diagramRestrictionHomEquiv K B W.flip
      (h ≫ (OrdinaryDiscreteMapping.mappingIso B W).hom)
  calc
    diagramRestrictionHomEquiv K A W.flip
        ((h ≫ diagramMappingPrecomp (discrete.map j) W) ≫
          (OrdinaryDiscreteMapping.mappingIso A W).hom) =
      diagramRestrictionHomEquiv K A W.flip
        (h ≫ ((OrdinaryDiscreteMapping.mappingIso B W).hom ≫
          DaggerNativeBisimplicialHorizontalMapping.horizontalPre j W)) := by
      rw [Category.assoc, OrdinaryDiscreteMapping.mappingIso_natural]
    _ = diagramRestrictionHomEquiv K A W.flip
          ((h ≫ (OrdinaryDiscreteMapping.mappingIso B W).hom) ≫
            diagramHomPrecomp j W.flip) := by
      rw [Category.assoc]
      rfl
    _ = j ≫ diagramRestrictionHomEquiv K B W.flip
          (h ≫ (OrdinaryDiscreteMapping.mappingIso B W).hom) :=
      diagramRestrictionHomEquiv_coeff K j _

/-- The inverse transpose commutes with vertical restriction. -/
theorem transpose_symm_pre {K L A : SSet.{0}} (v : K ⟶ L) (W : Space)
    (g : A ⟶ diagramRestriction L W.flip) :
    (transpose K A W).symm (g ≫ diagramRestrictionPre v W.flip) =
      v ≫ (transpose L A W).symm g := by
  apply (transpose K A W).injective
  rw [Equiv.apply_symm_apply, transpose_pre, Equiv.apply_symm_apply]

/-- The inverse transpose commutes with horizontal precomposition. -/
theorem transpose_symm_coeff {K A B : SSet.{0}} (j : A ⟶ B) (W : Space)
    (g : B ⟶ diagramRestriction K W.flip) :
    (transpose K A W).symm (j ≫ g) =
      (transpose K B W).symm g ≫ diagramMappingPrecomp (discrete.map j) W := by
  apply (transpose K A W).injective
  rw [Equiv.apply_symm_apply, transpose_coeff, Equiv.apply_symm_apply]

/-- The literal simplex-to-groupoid unit is the horizontal coefficient map
in the original walking restriction square. -/
theorem simplexUnit_transpose (K : SSet.{0}) (W : Space)
    (h : K ⟶ diagramMappingSpace
      (discrete.obj (GroupoidSimplex.parameter.obj ⦋1⦌)) W) :
    transpose K (Δ[1] : SSet.{0}) W
        (h ≫ diagramMappingPrecomp
          (discrete.map (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)) W) =
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫
        transpose K (GroupoidSimplex.parameter.obj ⦋1⦌) W h :=
  transpose_coeff (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) W h

#print axioms transpose
#print axioms transpose_pre
#print axioms transpose_coeff
#print axioms transpose_symm_pre
#print axioms transpose_symm_coeff
#print axioms simplexUnit_transpose

end

end DaggerModels.PartII.OrdinarySegalRestrictionTranspose
