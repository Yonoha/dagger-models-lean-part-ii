import NativeSimplexIndexResolutionNaturality
import NativeGroupoidCompletionNerveBaseCases
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
import Mathlib.CategoryTheory.Elements
import NativeNerveOppositeIso

/-!
# The original standard-simplex resolution as a natural weak span

The existing entire-simplex resolution maps are used literally. Both weak
legs are natural in every original simplicial-set map, in universe zero.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSimplexIndexResolution DaggerNativeSimplexIndexResolutionNaturality
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SimplicialResolutionFunctor

noncomputable section

private theorem indexMap_id (X : SSet.{0}) : indexMap (𝟙 X) = 𝟭 (LiftedIndex X) := by
  have h := congrArg Cat.Hom.toFunctor ((CostructuredArrow.functor uliftYoneda).map_id X)
  change CostructuredArrow.map (𝟙 X) = 𝟭 (Index X) at h
  dsimp only [indexMap]
  rw [h]
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl)

private theorem indexMap_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    indexMap (f ≫ g) = indexMap f ⋙ indexMap g := by
  have h := congrArg Cat.Hom.toFunctor
    ((CostructuredArrow.functor uliftYoneda).map_comp f g)
  change CostructuredArrow.map (f ≫ g) = CostructuredArrow.map f ⋙
    CostructuredArrow.map g at h
  dsimp only [indexMap]
  rw [h]
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original lifted simplex index, functorial in the full original input. -/
def indexFunctor : SSet.{0} ⥤ Cat.{0,0} where
  obj X := Cat.of (LiftedIndex X)
  map f := (indexMap f).toCatHom
  map_id X := by apply Cat.Hom.ext; exact indexMap_id X
  map_comp f g := by apply Cat.Hom.ext; exact indexMap_comp f g

/-- The original entire standard-simplex resolution, with all map laws. -/
def resolutionFunctor : SSet.{0} ⥤ SSet.{0} where
  obj X := DaggerBisimplicialDiagonal.diag (resolution X)
  map f := resolutionMap f
  map_id X := by
    apply NatTrans.ext
    funext q x
    change (⟨x.1 ⋙ indexMap (𝟙 X), x.2⟩ :
      (DaggerBisimplicialDiagonal.diag (resolution X)).obj q) = x
    have h : x.1 ⋙ indexMap (𝟙 X) = x.1 := by rw [indexMap_id]; rfl
    exact Sigma.ext h HEq.rfl
  map_comp {X Y Z} f g := by
    apply NatTrans.ext
    funext q x
    change (⟨x.1 ⋙ indexMap (f ≫ g), x.2⟩ :
      (DaggerBisimplicialDiagonal.diag (resolution Z)).obj q) =
      ⟨(x.1 ⋙ indexMap f) ⋙ indexMap g, x.2⟩
    have h : x.1 ⋙ indexMap (f ≫ g) = (x.1 ⋙ indexMap f) ⋙ indexMap g := by
      rw [indexMap_comp]
      rfl
    exact Sigma.ext h HEq.rfl

/-- The actual full lifted-index nerves, with every map retained. -/
def liftedIndexNerve : SSet.{0} ⥤ SSet.{0} := indexFunctor ⋙ nerveFunctor

/-- The retained exact full-simplex augmentation is a natural transformation. -/
def augmentation : resolutionFunctor ⟶ 𝟭 (SSet.{0}) where
  app X := toOriginal X
  naturality {_ _} f := augmentation_square f

/-- The retained exact full-index projection is also natural. -/
def projection : resolutionFunctor ⟶ liftedIndexNerve where
  app X := toLiftedNerve X
  naturality {_ _} f := projection_square f

/-- The augmentation leg is Kan weak for every input without fibrancy. -/
theorem augmentation_weak (X : SSet.{0}) : WeakEquivalence (augmentation.app X) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNativeSimplexIndexNerveWeakContractibility.toOriginal_GW X)

/-- The actual full-index projection leg is Kan weak for every input. -/
theorem projection_weak (X : SSet.{0}) : WeakEquivalence (projection.app X) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (toLiftedNerve_GW X)

/-- The actual opposite-Elements category is a functor of the full input. -/
def elementsOpposite : SSet.{0} ⥤ Cat.{0,0} := Functor.elementsFunctor ⋙ Cat.opFunctor

private def elementsEquiv (X : SSet.{0}) : X.Elementsᵒᵖ ≌ Index X :=
  CategoryOfElements.costructuredArrowULiftYonedaEquivalence X

/-- Exact Mathlib simplex/Elements comparison, natural in the original input. -/
def toElements : indexFunctor ⟶ elementsOpposite where
  app X := (ULiftHom.down ⋙ (elementsEquiv X).inverse).toCatHom
  naturality {_ _} f := by
    apply Cat.Hom.ext
    rfl

/-- The entire original resolution maps naturally to the actual Elements nerve. -/
def elementsProjection : resolutionFunctor ⟶ elementsOpposite ⋙ nerveFunctor :=
  projection ≫ Functor.whiskerRight toElements nerveFunctor

/-- The exact opposite-Elements leg is Kan weak on every full original input. -/
theorem elementsProjection_weak (X : SSet.{0}) :
    WeakEquivalence (elementsProjection.app X) := by
  have : WeakEquivalence (projection.app X) := projection_weak X
  have : IsIso (DaggerNativeSmallHomNerveLift.downMap (Index X)) :=
    (DaggerNativeSmallHomNerveLift.iso (Index X)).isIso_inv
  have : WeakEquivalence (nerveMap (elementsEquiv X).inverse) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  change WeakEquivalence (projection.app X ≫
    (DaggerNativeSmallHomNerveLift.downMap (Index X) ≫
      nerveMap (elementsEquiv X).inverse))
  infer_instance

end

end DaggerModels.PartII.SimplicialResolutionFunctor
