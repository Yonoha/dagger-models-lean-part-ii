import OrdinarySegalCotensorProductIso

/-!
# Naturality of cotensor association in the outer parameter

The exact product comparison respects contravariant precomposition in
the outer parameter. The tensor source on the right is literally the
map induced by `B ◁ f`, with the same original factor order.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalCotensorProductParameterNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalCotensorProductIso (productIso rowIso associatorMappingIso)

noncomputable section

private theorem associatorMappingIso_natural_middle (B D : SSet.{0})
    {A A' : SSet.{0}} (f : A ⟶ A') (W : Space) :
    diagramMappingPrecomp (discrete.map (B ◁ (f ▷ D))) W ≫
        (associatorMappingIso B A D W).hom =
      (associatorMappingIso B A' D W).hom ≫
        diagramMappingPrecomp (discrete.map ((B ◁ f) ▷ D)) W := by
  change diagramMappingPrecomp (discrete.map (B ◁ (f ▷ D))) W ≫
      diagramMappingPrecomp (discrete.map (α_ B A D).hom) W =
    diagramMappingPrecomp (discrete.map (α_ B A' D).hom) W ≫
      diagramMappingPrecomp (discrete.map ((B ◁ f) ▷ D)) W
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp, ← discrete.map_comp]
  exact congrArg (fun g ↦ diagramMappingPrecomp (discrete.map g) W)
    (MonoidalCategory.associator_naturality_middle B f D).symm

/-- The full cotensor product comparison is natural in the original
outer horizontal parameter. -/
theorem productIso_natural_outer (B : SSet.{0})
    {A A' : SSet.{0}} (f : A ⟶ A') (W : Space) :
    pre f (cotensor B W) ≫ (productIso A B W).hom =
      (productIso A' B W).hom ≫ pre (B ◁ f) W := by
  apply NatTrans.ext
  funext n
  change diagramMappingPrecomp
      (discrete.map (f ▷ SSet.stdSimplex.obj n.unop)) (cotensor B W) ≫
        (OrdinarySegalCotensorMappingIso.mappingIso B
          (A ⊗ SSet.stdSimplex.obj n.unop) W).hom ≫
        (associatorMappingIso B A (SSet.stdSimplex.obj n.unop) W).hom =
      (OrdinarySegalCotensorMappingIso.mappingIso B
        (A' ⊗ SSet.stdSimplex.obj n.unop) W).hom ≫
        (associatorMappingIso B A' (SSet.stdSimplex.obj n.unop) W).hom ≫
          diagramMappingPrecomp
            (discrete.map ((B ◁ f) ▷ SSet.stdSimplex.obj n.unop)) W
  rw [← Category.assoc,
    OrdinarySegalCotensorMappingIso.mappingIso_natural_source B
      (f ▷ SSet.stdSimplex.obj n.unop) W,
    Category.assoc,
    associatorMappingIso_natural_middle B (SSet.stdSimplex.obj n.unop) f W,
    ← Category.assoc]

#print axioms productIso_natural_outer

end
end DaggerModels.PartII.OrdinarySegalCotensorProductParameterNaturality
