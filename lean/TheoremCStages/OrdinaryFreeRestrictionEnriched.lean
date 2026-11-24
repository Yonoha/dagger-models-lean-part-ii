import OrdinaryFreeRestrictionMapping
import DaggerModelsPartII.DiagramMappingLimits
import DaggerModelsPartII.DiagramTensorMappingAdjunction
import DaggerModelsPartII.JTReversalInput
import DaggerModelsPartII.JTRealizationDiagonal
import DaggerModelsPartII.JTProjectiveOrderedFiberComparison

/-!
# Enriched horizontal free-restriction comparison

The degreewise equivalence from `OrdinaryFreeRestrictionMapping` respects
the entire vertical simplicial direction. Its inverse is ordinary
restriction after tensoring the adjunction unit with a vertical simplex.
The literal `ordinaryInput` is then identified with that restriction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels

namespace DaggerModels.PartII.OrdinaryFreeRestrictionEnriched

noncomputable section

private abbrev Source := OrdinaryCSSLocalization.Space
private abbrev Target := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev inclusion := ReverseSimplex.inclusion
private abbrev extension := extendIndexLeft.{0, 0} inclusion
private abbrev restriction := restrictIndex.{0, 0} inclusion

/-- The inverse degreewise comparison is the unit, tensored with the
vertical simplex, followed by ordinary restriction of the target map. -/
private theorem levelEquiv_symm_apply (A : Source) (W : Target)
    (n : SimplexCategory)
    (θ : (diagramMappingSpace (extension.obj A) W).obj (op n)) :
    (OrdinaryFreeRestrictionMapping.levelEquiv A W n).symm θ =
      (simplicialPresheafProductRight.{0, 0} SimplexCategory
        (SSet.stdSimplex.obj n)).map
          ((extendIndexLeftAdjunction.{0, 0} inclusion).unit.app A) ≫
        restriction.map θ := by
  let K := SSet.stdSimplex.obj n
  let e := extendIndexLeft_productRight.{0, 0} inclusion K
  let a := extendIndexLeftAdjunction.{0, 0} inclusion
  change (a.homEquiv _ W) (e.hom.app A ≫ θ) = _
  rw [a.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ restriction.map θ)
    (extendIndexLeft_unit_productRight.{0, 0} inclusion A K)

/-- Tensoring the horizontal adjunction unit is natural in every
vertical simplex operator. -/
private theorem tensorUnit_natural (A : Source)
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    (diagramTensor A).map (SSet.stdSimplex.map f.unop) ≫
        (simplicialPresheafProductRight.{0, 0} SimplexCategory
          (SSet.stdSimplex.obj m.unop)).map
            ((extendIndexLeftAdjunction.{0, 0} inclusion).unit.app A) =
      (simplicialPresheafProductRight.{0, 0} SimplexCategory
          (SSet.stdSimplex.obj n.unop)).map
            ((extendIndexLeftAdjunction.{0, 0} inclusion).unit.app A) ≫
        restriction.map ((diagramTensor (extension.obj A)).map
          (SSet.stdSimplex.map f.unop)) := by
  apply NatTrans.ext
  funext c
  let u := (extendIndexLeftAdjunction.{0, 0} inclusion).unit.app A
  change A.obj c ◁ SSet.stdSimplex.map f.unop ≫
      u.app c ▷ SSet.stdSimplex.obj m.unop =
    u.app c ▷ SSet.stdSimplex.obj n.unop ≫
      (restriction.obj (extension.obj A)).obj c ◁
        SSet.stdSimplex.map f.unop
  exact whisker_exchange (u.app c) (SSet.stdSimplex.map f.unop)

/-- Ordinary restriction of a map after horizontal extension commutes
with every original vertical simplicial operator. -/
private theorem levelEquiv_symm_natural (A : Source) (W : Target)
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    (θ : (diagramMappingSpace (extension.obj A) W).obj m) :
    (OrdinaryFreeRestrictionMapping.levelEquiv A W n.unop).symm
        ((diagramMappingSpace (extension.obj A) W).map f θ) =
      (diagramMappingSpace A (restriction.obj W)).map f
        ((OrdinaryFreeRestrictionMapping.levelEquiv A W m.unop).symm θ) := by
  rw [levelEquiv_symm_apply, levelEquiv_symm_apply]
  change
    (simplicialPresheafProductRight.{0, 0} SimplexCategory
        (SSet.stdSimplex.obj n.unop)).map
          ((extendIndexLeftAdjunction.{0, 0} inclusion).unit.app A) ≫
      restriction.map
        ((diagramTensor (extension.obj A)).map
          (SSet.stdSimplex.map f.unop) ≫ θ) =
    (diagramTensor A).map (SSet.stdSimplex.map f.unop) ≫
      ((simplicialPresheafProductRight.{0, 0} SimplexCategory
          (SSet.stdSimplex.obj m.unop)).map
            ((extendIndexLeftAdjunction.{0, 0} inclusion).unit.app A) ≫
        restriction.map θ)
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun h ↦ h ≫ restriction.map θ)
      (tensorUnit_natural A f).symm

/-- The actual simplicial mapping space into horizontal restriction is
isomorphic to mapping out of the exact horizontal left extension. -/
def mappingRestrictionIso (A : Source) (W : Target) :
    diagramMappingSpace A (restriction.obj W) ≅
      diagramMappingSpace (extension.obj A) W :=
  NatIso.ofComponents
    (fun n ↦ (OrdinaryFreeRestrictionMapping.levelEquiv A W n.unop).toIso)
    (by
      intro m n f
      funext η
      change
        (OrdinaryFreeRestrictionMapping.levelEquiv A W n.unop)
            ((diagramMappingSpace A (restriction.obj W)).map f η) =
          (diagramMappingSpace (extension.obj A) W).map f
            ((OrdinaryFreeRestrictionMapping.levelEquiv A W m.unop) η)
      apply (OrdinaryFreeRestrictionMapping.levelEquiv A W n.unop).symm.injective
      simpa only [Equiv.symm_apply_apply] using
        (levelEquiv_symm_natural A W f
          ((OrdinaryFreeRestrictionMapping.levelEquiv A W m.unop) η)).symm)

/-- Curry of the literal two-index input is horizontal restriction of
the original reversal diagram, with identity on every inner simplex. -/
def inputRestrictionIso (W : Target) :
    JTRealizationDiagonal.ordinaryCurry.obj
        (JTReversalInput.ordinaryInput.obj W) ≅ restriction.obj W :=
  NatIso.ofComponents
    (fun m ↦ JTProjectiveOrderedFiberComparison.rowRestrictionIso W m.unop)
    (by
      intro m n f
      apply NatTrans.ext
      funext q x
      dsimp [JTProjectiveOrderedFiberComparison.rowRestrictionIso,
        JTProjectiveOrderedFiberComparison.row,
        JTRealizationDiagonal.ordinaryCurry,
        JTReversalInput.ordinaryInput, restriction, restrictIndex]
      simp)

/-- For every original ordinary horizontal simplicial set, the strict
mapping space of its discrete image into the actual ordinary input is
the strict mapping space of its free dagger image into the same `W`. -/
def freeDiscreteMappingIso (K : SSet.{0}) (W : Target) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj K)
        (JTRealizationDiagonal.ordinaryCurry.obj
          (JTReversalInput.ordinaryInput.obj W)) ≅
      diagramMappingSpace
        (ReversalDiscreteFreeColimits.discreteFree.obj K) W :=
  (diagramMappingTarget (OrdinaryCSSLocalization.discrete.obj K)).mapIso
      (inputRestrictionIso W) ≪≫
    mappingRestrictionIso (OrdinaryCSSLocalization.discrete.obj K) W ≪≫
      ((diagramMappingSource W).mapIso
        ((OrdinaryFreeDiscreteKan.discreteExtensionIso.app K).op)).symm

#print axioms mappingRestrictionIso
#print axioms inputRestrictionIso
#print axioms freeDiscreteMappingIso

end

end DaggerModels.PartII.OrdinaryFreeRestrictionEnriched
