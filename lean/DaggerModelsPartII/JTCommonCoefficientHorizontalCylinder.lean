import DaggerModelsPartII.JTCommonCoefficientBeadLift
import DaggerModelsPartII.JTGraphInterpolatedSourceComparison
import DaggerModelsPartII.JTMixedGraphHorizontalTraversal

/-! # Horizontal naturality of common-coefficient cylinders -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCommonCoefficientHorizontalCylinder

open JTNecklaceEndpointCylinder
open JTHigherInterleavedParameter (common)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- The common-coefficient cylinder is natural for every native necklace map. -/
theorem cylinderMap_source {S T : NecklaceCode} (u : S ⟶ T)
    {k b : SimplexCategory} (c : k ⟶ b) (s : T.toSSet ⟶ J.obj k)
    (n : SimplexCategory) :
    JTCommonCoefficientParameter.cylinderMap S c (u.map ≫ s) n ≫
        nativeMap u (common k n) =
      nativeMap u n ≫ JTCommonCoefficientParameter.cylinderMap T c s n := by
  apply (isPushout S n).hom_ext
  · rw [← Category.assoc, JTCommonCoefficientParameter.cylinderMap_cylinder,
      Category.assoc, nativeMap_cylinder]
    rw [← Category.assoc ((cylinder S).app n), nativeMap_cylinder,
      Category.assoc, JTCommonCoefficientParameter.cylinderMap_cylinder]
    rw [← Category.assoc, ← JTCommonCoefficientParameter.graphPrism_natural]
    simp only [Category.assoc]
  · rw [← Category.assoc, JTCommonCoefficientParameter.cylinderMap_boundary,
      nativeMap_boundary, ← Category.assoc, nativeMap_boundary,
      JTCommonCoefficientParameter.cylinderMap_boundary]

/-- Horizontal, coefficient, and injective time operators commute on the
actual padded common-coefficient cylinder. -/
theorem cylinderMap_padded_mixed {d e : ℕ} {k l b n m : SimplexCategory}
    (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0)
    (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    {c : k ⟶ b} {c' : l ⟶ b} (f : k ⟶ l) (hf : f ≫ c' = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (s : SSet.stdSimplex.obj ⦋d⦌ ⟶ J.obj k)
    (t : SSet.stdSimplex.obj ⦋e⦌ ⟶ J.obj l)
    (hs : s ≫ J.map f = SSet.stdSimplex.map a ≫ t) :
    JTCommonCoefficientParameter.cylinderMap
          (MixedGraphCylinderTraversal.code d) c
          (JTMixedGraphRawRefinement.nativeGraphParameter s) n ≫
        (value (MixedGraphCylinderTraversal.code d)).map
          (JTCommonCoefficientParameter.map f hf j hj) ≫
        nativeMap (JTMixedGraphHorizontalTraversal.padded
          (JTMixedGraphHorizontalTraversal.singleOperator a h₀ h₁)) (common l m) =
      (value (MixedGraphCylinderTraversal.code d)).map j ≫
        nativeMap (JTMixedGraphHorizontalTraversal.padded
          (JTMixedGraphHorizontalTraversal.singleOperator a h₀ h₁)) m ≫
        JTCommonCoefficientParameter.cylinderMap
          (MixedGraphCylinderTraversal.code e) c'
          (JTMixedGraphRawRefinement.nativeGraphParameter t) m := by
  let u := JTMixedGraphHorizontalTraversal.padded
    (JTMixedGraphHorizontalTraversal.singleOperator a h₀ h₁)
  have hp : JTMixedGraphRawRefinement.nativeGraphParameter s ≫ J.map f =
      u.map ≫ JTMixedGraphRawRefinement.nativeGraphParameter t :=
    JTMixedGraphHorizontalTraversal.parameter_mixed a h₀ h₁ f hs
  rw [← Category.assoc,
    JTCommonCoefficientParameter.cylinderMap_map
      (MixedGraphCylinderTraversal.code d) f hf j hj
      (JTMixedGraphRawRefinement.nativeGraphParameter s)
      (u.map ≫ JTMixedGraphRawRefinement.nativeGraphParameter t) hp]
  rw [Category.assoc, cylinderMap_source u c' (JTMixedGraphRawRefinement.nativeGraphParameter t) m]

/-- The same mixed square for the maps under the original endpoints. -/
theorem commonToDecorated_padded_mixed {d e : ℕ} {k l b n m : SimplexCategory}
    (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0)
    (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    {c : k ⟶ b} {c' : l ⟶ b} (f : k ⟶ l) (hf : f ≫ c' = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (s : SSet.stdSimplex.obj ⦋d⦌ ⟶ J.obj k)
    (t : SSet.stdSimplex.obj ⦋e⦌ ⟶ J.obj l)
    (hs : s ≫ J.map f = SSet.stdSimplex.map a ≫ t) :
    JTHigherMixedGraphTargetLift.commonToDecorated (n := n) c s ≫
        (under (MixedGraphCylinderTraversal.code d)).map
          (JTCommonCoefficientParameter.map f hf j hj) ≫
        JTGraphInterpolatedSourceComparison.sourceMap (JTMixedGraphHorizontalTraversal.padded
          (JTMixedGraphHorizontalTraversal.singleOperator a h₀ h₁)) (common l m) =
      (under (MixedGraphCylinderTraversal.code d)).map j ≫
        JTGraphInterpolatedSourceComparison.sourceMap (JTMixedGraphHorizontalTraversal.padded
          (JTMixedGraphHorizontalTraversal.singleOperator a h₀ h₁)) m ≫
        JTHigherMixedGraphTargetLift.commonToDecorated (n := m) c' t := by
  apply Under.UnderMorphism.ext
  exact cylinderMap_padded_mixed a h₀ h₁ f hf j hj s t hs

end

end DaggerModels.PartII.JTCommonCoefficientHorizontalCylinder
