import OrdinarySegalCotensorMappingIso
import OrdinarySegalCotensorParameterNaturality
import OrdinarySegalHorizontalCotensorPoint

/-!
# Associating the original horizontal cotensors

The checked strict Fubini map followed by the native Cartesian
associator identifies two successive cotensors with cotensoring by the
ordered product of their original parameters. Both independent
parameters and every horizontal simplex operator are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalCotensorProductIso

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalCotensorMappingIso (mappingIso)

noncomputable section

/-- Move the brackets in the complete original mapping-space weight. -/
def associatorMappingIso (B A D : SSet.{0}) (W : Space) :
    diagramMappingSpace (discrete.obj (B ⊗ (A ⊗ D))) W ≅
      diagramMappingSpace (discrete.obj ((B ⊗ A) ⊗ D)) W :=
  (diagramMappingSource W).mapIso
    (Iso.op (discrete.mapIso (α_ B A D)))

private theorem associatorMappingIso_hom (B A D : SSet.{0}) (W : Space) :
    (associatorMappingIso B A D W).hom =
      diagramMappingPrecomp (discrete.map (α_ B A D).hom) W := rfl

/-- The associator intertwines every unchanged horizontal operator. -/
theorem associatorMappingIso_natural (B A : SSet.{0}) (W : Space)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    diagramMappingPrecomp
        (discrete.map (B ◁ (A ◁ SSet.stdSimplex.map θ))) W ≫
        (associatorMappingIso B A (SSet.stdSimplex.obj m) W).hom =
      (associatorMappingIso B A (SSet.stdSimplex.obj n) W).hom ≫
        diagramMappingPrecomp
          (discrete.map ((B ⊗ A) ◁ SSet.stdSimplex.map θ)) W := by
  rw [associatorMappingIso_hom, associatorMappingIso_hom,
    ← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp, ← discrete.map_comp]
  exact congrArg (fun g ↦ diagramMappingPrecomp (discrete.map g) W)
    (MonoidalCategory.associator_naturality_right B A (SSet.stdSimplex.map θ)).symm

/-- The iterated cotensor at one original horizontal simplex degree. -/
def rowIso (A B : SSet.{0}) (W : Space) (n : SimplexCategory) :
    (cotensor A (cotensor B W)).obj (op n) ≅
      (cotensor (B ⊗ A) W).obj (op n) :=
  mappingIso B (A ⊗ SSet.stdSimplex.obj n) W ≪≫
    associatorMappingIso B A (SSet.stdSimplex.obj n) W

/-- The full natural isomorphism, with the original ordered product
`B ⊗ A` fixed by contravariance of horizontal cotensoring. -/
def productIso (A B : SSet.{0}) (W : Space) :
    cotensor A (cotensor B W) ≅ cotensor (B ⊗ A) W :=
  NatIso.ofComponents (fun n ↦ rowIso A B W n.unop) (by
    intro n m θ
    change diagramMappingPrecomp
        (discrete.map (A ◁ SSet.stdSimplex.map θ.unop)) (cotensor B W) ≫
          (mappingIso B (A ⊗ SSet.stdSimplex.obj m.unop) W).hom ≫
          (associatorMappingIso B A (SSet.stdSimplex.obj m.unop) W).hom =
        (mappingIso B (A ⊗ SSet.stdSimplex.obj n.unop) W).hom ≫
          (associatorMappingIso B A (SSet.stdSimplex.obj n.unop) W).hom ≫
            diagramMappingPrecomp
              (discrete.map ((B ⊗ A) ◁ SSet.stdSimplex.map θ.unop)) W
    rw [← Category.assoc,
      OrdinarySegalCotensorMappingIso.mappingIso_natural_source B
        (A ◁ SSet.stdSimplex.map θ.unop) W,
      Category.assoc, associatorMappingIso_natural B A W θ.unop,
      ← Category.assoc]
    )

#print axioms associatorMappingIso_natural
#print axioms rowIso
#print axioms productIso

end
end DaggerModels.PartII.OrdinarySegalCotensorProductIso
