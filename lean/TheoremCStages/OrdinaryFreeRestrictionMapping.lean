import OrdinaryFreeDiscreteKan
import DaggerModelsPartII.DiagramMappingSpace
import DaggerModelsPartII.IndexKanExtensions

/-!
# Mapping into a restricted reversal diagram

Left Kan extension along the ordinary simplex inclusion is adjoint to
horizontal restriction. Its compatibility with a fixed vertical simplex
gives the exact mapping-set equivalence in each vertical degree. The
enriched naturality and the identification with `ordinaryInput` are the
next stages; no Segal or completeness assertion is made here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerModels

namespace DaggerModels.PartII.OrdinaryFreeRestrictionMapping

noncomputable section

private abbrev Source := OrdinaryCSSLocalization.Space
private abbrev Target := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev inclusion := ReverseSimplex.inclusion
private abbrev extension := extendIndexLeft.{0, 0} inclusion
private abbrev restriction := restrictIndex.{0, 0} inclusion

/-- At one vertical simplex, mapping into the literal horizontal
restriction is equivalent to mapping out of horizontal left extension.
The tensor comparison retains the entire ordinary source `A`. -/
def levelEquiv (A : Source) (W : Target) (n : SimplexCategory) :
    (diagramMappingSpace A (restriction.obj W)).obj (op n) ≃
      (diagramMappingSpace (extension.obj A) W).obj (op n) := by
  let K := SSet.stdSimplex.obj n
  let e := extendIndexLeft_productRight.{0, 0} inclusion K
  let a := extendIndexLeftAdjunction.{0, 0} inclusion
  let T := simplicialPresheafProductRight.{0, 0}
  have hA : (diagramTensor A).obj K = (T SimplexCategory K).obj A := rfl
  have hL : (diagramTensor (extension.obj A)).obj K =
      (T ReverseSimplex K).obj (extension.obj A) := rfl
  refine {
    toFun := fun η ↦ e.inv.app A ≫
      (a.homEquiv ((T SimplexCategory K).obj A) W).symm η
    invFun := fun θ ↦ (a.homEquiv ((T SimplexCategory K).obj A) W)
      (e.hom.app A ≫ θ)
    left_inv := ?_
    right_inv := ?_ }
  · intro η
    change (a.homEquiv ((T SimplexCategory K).obj A) W)
      (e.hom.app A ≫
        (e.inv.app A ≫
          (a.homEquiv ((T SimplexCategory K).obj A) W).symm η)) = η
    rw [← Category.assoc, Iso.hom_inv_id_app]
    exact (congrArg (a.homEquiv ((T SimplexCategory K).obj A) W)
      (Category.id_comp _)).trans ((a.homEquiv _ W).apply_symm_apply η)
  · intro θ
    change e.inv.app A ≫
      (a.homEquiv ((T SimplexCategory K).obj A) W).symm
        ((a.homEquiv ((T SimplexCategory K).obj A) W)
          (e.hom.app A ≫ θ)) = θ
    rw [(a.homEquiv _ W).symm_apply_apply]
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

#print axioms levelEquiv

end

end DaggerModels.PartII.OrdinaryFreeRestrictionMapping
