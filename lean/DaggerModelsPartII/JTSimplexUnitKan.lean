import DaggerModelsPartII.JTParameterVertexKan
import NativeGroupoidCompletionNerveBaseCases
import TopCatModelCategory.SSet.NonDegenerateProdSimplex

/-!
# The original simplex-to-groupoid unit is a Kan trivial cofibration

The factorization uses the standard simplex nerve isomorphism and the
retained free-groupoid theorem for a category with an initial object.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSimplexUnitKan

open GroupoidSimplex JTCylinderCEComparison
open DaggerNativeGroupoidCompletionNerveBaseCases

noncomputable section

private def unlift (k : SimplexCategory) :
    ULift.{0} (Fin (k.len + 1)) ≌ Fin (k.len + 1) :=
  ULift.orderIso.equivalence

/-- The full original unit is the nerve of the actual free-groupoid unit,
precomposed with the standard-simplex comparison and the vertex unlift. -/
theorem simplexUnit_factor (k : SimplexCategory) :
    simplexUnit.app k =
      (SSet.stdSimplex.isoNerve.{0} k.len).hom ≫
        nerveMap (unlift k).functor ≫ nerveMap (FreeGroupoid.of (Fin (k.len + 1))) := by
  letI : Quiver.IsThin (completion k) :=
    DaggerOriginalInitialCategoryCompletionThin.completionIsThin
      (0 : Fin (k.len + 1)) (Fin.isInitialZero _)
  apply NatTrans.ext
  funext q a
  apply nerve.ext_of_isThin
  funext i
  rfl

/-- The actual component has injective simplicial levels. -/
theorem simplexUnit_mono (k : SimplexCategory) : Mono (simplexUnit.app k) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro a b h
  apply SSet.stdSimplex.objEquiv.injective
  ext i
  have hi := congrArg (fun (f : (parameter.obj k).obj q) ↦ (f.obj i).as.as) h
  exact congrArg Fin.val hi

/-- The original unit is weak in the Kan model at every parameter degree. -/
theorem simplexUnit_weak (k : SimplexCategory) : WeakEquivalence (simplexUnit.app k) := by
  haveI : WeakEquivalence (nerveMap (unlift k).functor) := nerveMap_weak_of_equivalence _
  haveI : WeakEquivalence (nerveMap (FreeGroupoid.of (Fin (k.len + 1)))) :=
    unit_nerve_weak_of_initial 0 (Fin.isInitialZero _)
  rw [simplexUnit_factor]
  infer_instance

theorem simplexUnit_cofibration (k : SimplexCategory) : Cofibration (simplexUnit.app k) := by
  haveI := simplexUnit_mono k
  exact (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance

end

end DaggerModels.PartII.JTSimplexUnitKan
