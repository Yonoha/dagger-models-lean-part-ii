import OrdinaryGroupoidSimplexCotensorHomotopyInverse
import OrdinarySegalCotensorProductUnit
import OrdinarySegalPrecompletion

/-!
# The coherent contraction is constant on the original image

Precomposing the whole groupoid-parameter contraction with the original
constant section gives the constant section of the parameter product.
The checked cotensor product isomorphism identifies this with the
constant E[1]-time path of the same image. No pointwise replacement of
the whole homotopy is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorConstantHomotopy

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorProductIso (productIso)

noncomputable section

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k

/-- At every original input object, the entire coherent contraction
agrees with the constant E[1]-path in the cotensor. -/
theorem constantSection_homotopy (k : SimplexCategory)
    (j : Fin (k.len + 1)) (W : Space) :
    constantSection (E k) W ≫
        OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W =
      constantSection (E k) W ≫
        constantSection (E ⦋1⦌) (cotensor (E k) W) := by
  let F := productIso (E ⦋1⦌) (E k) W
  apply (cancel_mono F.hom).mp
  have hpre := OrdinarySegalPrecompletion.constantSection_pre
    (OrdinaryGroupoidSimplexCoherentContraction.contraction k j) W
  have hprod := OrdinarySegalCotensorProductUnit.constantSection_product
    (E ⦋1⦌) (E k) W
  change (constantSection (E k) W ≫
      (pre (OrdinaryGroupoidSimplexCoherentContraction.contraction k j) W ≫
        F.inv)) ≫ F.hom =
    (constantSection (E k) W ≫
      constantSection (E ⦋1⦌) (cotensor (E k) W)) ≫ F.hom
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    hpre]
  exact hprod.symm

#print axioms constantSection_homotopy

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorConstantHomotopy
