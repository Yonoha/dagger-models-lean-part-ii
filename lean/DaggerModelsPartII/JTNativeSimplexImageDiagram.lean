import DaggerModelsPartII.JTNativeSimplexImage
import ChosenNecklaceCategory

/-!
# Coherent image faces for a diagram of necklace simplices

The ordinal image of each actual simplex gives a diagram of selected faces.
The degeneracies from the original simplices form a natural transformation,
and the resulting face diagram recovers the original diagram exactly.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeSimplexImageDiagram

noncomputable section

local instance : SmallCategory NecklaceCode := NecklaceCode.category

variable {I : Type*} [SmallCategory I]
variable (D : I ⥤ SimplexCategory) (T : I ⥤ NecklaceCode)
variable (g : D ⋙ SSet.stdSimplex.{0} ⟶ T ⋙ NecklaceCode.simplicialFunctor.{0})

private abbrev selected (i : I) :
    JTNativeSimplexImage.Factor (T.obj i) (D.obj i).len (g.app i) :=
  JTNativeSimplexImage.factor (T.obj i) (D.obj i).len (g.app i)

private theorem triangle {i j : I} (f : i ⟶ j) :
    g.app i ≫ NecklaceCode.simplicialFunctor.{0}.map (T.map f) =
      SSet.stdSimplex.{0}.map (D.map f) ≫ g.app j := by
  simpa only [Functor.comp_map] using (g.naturality f).symm

/-- The selected image degrees and the induced face operators form a functor. -/
def imageDegree (D : I ⥤ SimplexCategory) (T : I ⥤ NecklaceCode)
    (g : D ⋙ SSet.stdSimplex.{0} ⟶ T ⋙ NecklaceCode.simplicialFunctor.{0}) :
    I ⥤ SimplexCategory where
  obj i := (selected D T g i).middle
  map {i j} f := JTNativeSimplexImage.faceOperator
    (T := T.obj i) (U := T.obj j) (d := (D.obj i).len) (e := (D.obj j).len)
    (g.app i) (g.app j) (D.map f)
  map_id i := by
    simpa only [D.map_id, SimplexCategory.mk_len] using
      JTNativeSimplexImage.faceOperator_id (T.obj i) (D.obj i).len (g.app i)
  map_comp {i j k} f h := by
    simpa only [D.map_comp] using JTNativeSimplexImage.faceOperator_comp
      (T := T.obj i) (U := T.obj j) (V := T.obj k)
      (d := (D.obj i).len) (e := (D.obj j).len) (k := (D.obj k).len)
      (g.app i) (g.app j) (g.app k)
      (NecklaceCode.simplicialFunctor.{0}.map (T.map f))
      (NecklaceCode.simplicialFunctor.{0}.map (T.map h))
      (D.map f) (D.map h) (triangle D T g f) (triangle D T g h)

/-- The ordinal image quotient is natural in the diagram. -/
def quotient (D : I ⥤ SimplexCategory) (T : I ⥤ NecklaceCode)
    (g : D ⋙ SSet.stdSimplex.{0} ⟶ T ⋙ NecklaceCode.simplicialFunctor.{0}) :
    D ⟶ imageDegree D T g where
  app i := by simpa only [SimplexCategory.mk_len] using (selected D T g i).epi
  naturality {i j} f := by
    exact (JTNativeSimplexImage.faceOperator_fac
      (T := T.obj i) (U := T.obj j) (d := (D.obj i).len) (e := (D.obj j).len)
      (g.app i) (g.app j)
      (NecklaceCode.simplicialFunctor.{0}.map (T.map f)) (D.map f)
      (triangle D T g f)).symm

/-- The selected faces are natural in the target necklace diagram. -/
def imageFace (D : I ⥤ SimplexCategory) (T : I ⥤ NecklaceCode)
    (g : D ⋙ SSet.stdSimplex.{0} ⟶ T ⋙ NecklaceCode.simplicialFunctor.{0}) :
    imageDegree D T g ⋙ SSet.stdSimplex.{0} ⟶
    T ⋙ NecklaceCode.simplicialFunctor.{0} where
  app i := (selected D T g i).face
  naturality {i j} f := by
    exact JTNativeSimplexImage.faceOperator_square
      (T := T.obj i) (U := T.obj j) (d := (D.obj i).len) (e := (D.obj j).len)
      (g.app i) (g.app j)
      (NecklaceCode.simplicialFunctor.{0}.map (T.map f)) (D.map f)
      (triangle D T g f)

/-- The diagram factorization is equal to the original natural transformation. -/
theorem quotient_imageFace :
    Functor.whiskerRight (quotient D T g) SSet.stdSimplex.{0} ≫ imageFace D T g = g := by
  apply NatTrans.ext
  funext i
  exact (selected D T g i).factor

end

end DaggerModels.PartII.JTNativeSimplexImageDiagram
