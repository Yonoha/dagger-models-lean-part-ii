import OrdinarySegalCotensorEndpointCorner
import OrdinarySegalCotensorParameterNaturality

/-!
# Boundary-one factors of the exact cotensor corner

The mapping space out of `K ⊗ ∂Δ[1]` is the ordered pair of degree-zero
rows of the original horizontal cotensor. This isomorphism commutes with
every parameter restriction. It is the bottom face of the relative
endpoint corner and carries no fibrancy or weak-equivalence assumption.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory Limits

namespace DaggerModels.PartII.OrdinarySegalCotensorEndpointCalibration

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre)

noncomputable section

private abbrev boundary := (SSet.boundary 1).toSSet

/-- The exact tensor-boundary mapping space is the ordered product of
the two original cotensor vertex rows. -/
def boundaryEndpointIso (K : SSet.{0}) (W : Space) :
    diagramMappingSpace (discrete.obj (K ⊗ boundary)) W ≅
      (cotensor K W).obj (op ⦋0⦌) ⨯
        (cotensor K W).obj (op ⦋0⦌) :=
  (OrdinarySegalCotensorMappingIso.mappingIso K boundary W).symm ≪≫
    OrdinarySegalCotensorBoundaryOne.endpointTargetIso (cotensor K W)

/-- The bottom face of the parameter-restriction corner is exactly
the original map on both ordered endpoint factors. -/
theorem boundaryEndpointIso_natural {K L : SSet.{0}} (f : K ⟶ L)
    (W : Space) :
    diagramMappingPrecomp (discrete.map (f ▷ boundary)) W ≫
        (boundaryEndpointIso K W).hom =
      (boundaryEndpointIso L W).hom ≫
        prod.map ((pre f W).app (op ⦋0⦌))
          ((pre f W).app (op ⦋0⦌)) := by
  let F (A : SSet.{0}) :=
    OrdinarySegalCotensorMappingIso.mappingIso A boundary W
  let P := diagramMappingPostcomp (discrete.obj boundary) (pre f W)
  let Q := diagramMappingPrecomp (discrete.map (f ▷ boundary)) W
  let E (A : SSet.{0}) :=
    OrdinarySegalCotensorBoundaryOne.endpointTargetIso (cotensor A W)
  have hF : Q ≫ (F K).inv = (F L).inv ≫ P := by
    apply (cancel_mono (F K).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Category.assoc,
      OrdinarySegalCotensorParameterNaturality.mappingIso_natural_parameter,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hE : P ≫ (E K).hom =
      (E L).hom ≫
        prod.map ((pre f W).app (op ⦋0⦌))
          ((pre f W).app (op ⦋0⦌)) :=
    OrdinarySegalCotensorEndpointCorner.endpointTargetIso_natural_target (pre f W)
  change Q ≫ ((F K).inv ≫ (E K).hom) =
    ((F L).inv ≫ (E L).hom) ≫
      prod.map ((pre f W).app (op ⦋0⦌))
        ((pre f W).app (op ⦋0⦌))
  rw [← Category.assoc, hF, Category.assoc, hE, ← Category.assoc]

#print axioms boundaryEndpointIso
#print axioms boundaryEndpointIso_natural

end
end DaggerModels.PartII.OrdinarySegalCotensorEndpointCalibration
