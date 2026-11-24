import BisimplicialCommaBarReconstruction
import BisimplicialRowBarAugmentation
import SimplicialReplacementPointwiseKan

/-!
# The full comma resolution reconstructs both original diagonals

The total comparison retains the original pullback total coordinate. The
base comparison evaluates the original whole standard-simplex parameter.
Their square agrees with the original arrow before taking the diagonal.
The designated original endpoint-pair comparison remains separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (replacement)
open DaggerNativeSimplicialReplacementWeightsChange (changeWeights)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialCommaDiagonalReconstruction

open BisimplicialBaseSimplexFibers (Index fiberDiagram simplexProjection)
open BisimplicialCommaBarReconstruction (totalBarMap totalBarMap_diagonal_weak)
open SimplicialReplacementColumnElements (replacementMap)

noncomputable section

/-- Every original base-simplex parameter on the unchanged full comma category. -/
def parameterDiagram (f : Arrow BiSSet.{0}) : Index f ⥤ SSet.{0} :=
  Comma.fst SSet.stdSimplex f.right ⋙ SSet.stdSimplex

/-- Evaluate the actual whole simplex in its original outer base row. -/
def parameterEvaluation (f : Arrow BiSSet.{0}) :
    parameterDiagram f ⟶ Comma.snd SSet.stdSimplex f.right ⋙ f.right where
  app σ := σ.hom
  naturality _ _ a := a.w

/-- The complete parameter bar maps to the original base-row bar. -/
def parameterBarMap (f : Arrow BiSSet.{0}) :
    replacement (parameterDiagram f) ⟶ replacement f.right :=
  replacementMap (Comma.snd SSet.stdSimplex f.right)
    (parameterDiagram f) f.right (parameterEvaluation f)

/-- The complete original pullback square is retained on both bars. -/
theorem bar_square (f : Arrow BiSSet.{0}) :
    changeWeights (simplexProjection f) ≫ parameterBarMap f =
      totalBarMap f ≫ changeWeights f.hom := by
  apply NatTrans.ext
  funext q
  apply NatTrans.ext
  funext k z
  rcases z with ⟨c, z⟩
  apply congrArg (fun t ↦
    (⟨c ⋙ Comma.snd SSet.stdSimplex f.right, t⟩ :
      DaggerNativeSimplicialReplacementCells.Cell f.right q k))
  exact (congrFun (NatTrans.congr_app
    (pullback.condition (f := f.hom.app (c.obj 0).right) (g := (c.obj 0).hom)) k) z).symm

/-- Identity-row fibers project isomorphically to their whole original simplex. -/
theorem identity_parameter_isIso (B : BiSSet.{0}) :
    IsIso (simplexProjection (Arrow.mk (𝟙 B))) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro σ
  change IsIso (pullback.snd (𝟙 (B.obj σ.right)) σ.hom)
  infer_instance

private theorem identity_bar_square (f : Arrow BiSSet.{0}) :
    changeWeights (simplexProjection (Arrow.mk (𝟙 f.right))) ≫ parameterBarMap f =
      totalBarMap (Arrow.mk (𝟙 f.right)) := by
  have hi : changeWeights (𝟙 f.right) = 𝟙 (replacement f.right) := by
    apply NatTrans.ext
    funext q
    apply NatTrans.ext
    rfl
  calc
    _ = totalBarMap (Arrow.mk (𝟙 f.right)) ≫ changeWeights (𝟙 f.right) :=
      bar_square (Arrow.mk (𝟙 f.right))
    _ = totalBarMap (Arrow.mk (𝟙 f.right)) ≫ 𝟙 _ :=
      congrArg (fun m ↦ totalBarMap (Arrow.mk (𝟙 f.right)) ≫ m) hi
    _ = _ := Category.comp_id _

/-- The parameter bar reconstructs the original base-row bar weakly. -/
theorem parameterBarMap_diagonal_weak (f : Arrow BiSSet.{0}) :
    WeakEquivalence (diagonalFunctor.map (parameterBarMap f)) := by
  let φ := simplexProjection (Arrow.mk (𝟙 f.right))
  have : IsIso φ := identity_parameter_isIso f.right
  have : WeakEquivalence (diagonalFunctor.map (changeWeights φ)) :=
    SimplicialReplacementPointwiseKan.diagonalChange_weak φ (fun σ ↦ by infer_instance)
  have : WeakEquivalence
      (diagonalFunctor.map (totalBarMap (Arrow.mk (𝟙 f.right)))) :=
    totalBarMap_diagonal_weak (Arrow.mk (𝟙 f.right))
  have h : diagonalFunctor.map (changeWeights φ) ≫
      diagonalFunctor.map (parameterBarMap f) =
    diagonalFunctor.map (totalBarMap (Arrow.mk (𝟙 f.right))) := by
    rw [← diagonalFunctor.map_comp]
    exact congrArg diagonalFunctor.map (identity_bar_square f)
  exact weakEquivalence_of_precomp_of_fac h

/-- The original comma fiber bar maps to the original total bisimplicial set. -/
def totalReconstruction (f : Arrow BiSSet.{0}) :
    replacement (fiberDiagram f) ⟶ f.left :=
  totalBarMap f ≫ BisimplicialRowBarAugmentation.augmentation f.left

/-- The whole original parameter bar maps to the original base bisimplicial set. -/
def baseReconstruction (f : Arrow BiSSet.{0}) :
    replacement (parameterDiagram f) ⟶ f.right :=
  parameterBarMap f ≫ BisimplicialRowBarAugmentation.augmentation f.right

/-- The full reconstruction square uses the original total-to-base map. -/
theorem reconstruction_square (f : Arrow BiSSet.{0}) :
    changeWeights (simplexProjection f) ≫ baseReconstruction f =
      totalReconstruction f ≫ f.hom := by
  calc
    _ = (changeWeights (simplexProjection f) ≫ parameterBarMap f) ≫
        BisimplicialRowBarAugmentation.augmentation f.right :=
      (Category.assoc _ _ _).symm
    _ = (totalBarMap f ≫ changeWeights f.hom) ≫
        BisimplicialRowBarAugmentation.augmentation f.right :=
      congrArg (fun m ↦ m ≫ BisimplicialRowBarAugmentation.augmentation f.right)
        (bar_square f)
    _ = totalBarMap f ≫
        (changeWeights f.hom ≫ BisimplicialRowBarAugmentation.augmentation f.right) :=
      Category.assoc _ _ _
    _ = totalBarMap f ≫
        (BisimplicialRowBarAugmentation.augmentation f.left ≫ f.hom) :=
      congrArg (fun m ↦ totalBarMap f ≫ m)
        (BisimplicialRowBarAugmentation.augmentation_natural f.hom)
    _ = _ := (Category.assoc _ _ _).symm

/-- The total diagonal comparison is weak with no Kan or fibration assumption. -/
theorem totalReconstruction_diagonal_weak (f : Arrow BiSSet.{0}) :
    WeakEquivalence (diagonalFunctor.map (totalReconstruction f)) := by
  have : WeakEquivalence (diagonalFunctor.map (totalBarMap f)) :=
    totalBarMap_diagonal_weak f
  have : WeakEquivalence
      (diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation f.left)) :=
    BisimplicialRowBarAugmentation.diagonal_weak f.left
  change WeakEquivalence
    (diagonalFunctor.map (totalBarMap f ≫ BisimplicialRowBarAugmentation.augmentation f.left))
  rw [diagonalFunctor.map_comp]
  infer_instance

/-- The base diagonal comparison is weak, with the same original parameter maps. -/
theorem baseReconstruction_diagonal_weak (f : Arrow BiSSet.{0}) :
    WeakEquivalence (diagonalFunctor.map (baseReconstruction f)) := by
  have : WeakEquivalence (diagonalFunctor.map (parameterBarMap f)) :=
    parameterBarMap_diagonal_weak f
  have : WeakEquivalence
      (diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation f.right)) :=
    BisimplicialRowBarAugmentation.diagonal_weak f.right
  change WeakEquivalence
    (diagonalFunctor.map (parameterBarMap f ≫ BisimplicialRowBarAugmentation.augmentation f.right))
  rw [diagonalFunctor.map_comp]
  infer_instance

#print axioms bar_square
#print axioms parameterBarMap_diagonal_weak
#print axioms reconstruction_square
#print axioms totalReconstruction_diagonal_weak
#print axioms baseReconstruction_diagonal_weak

end

end DaggerModels.PartII.BisimplicialCommaDiagonalReconstruction
