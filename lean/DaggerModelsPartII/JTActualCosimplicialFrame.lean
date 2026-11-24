import DaggerModelsPartII.JTRelativeReedyFrameProperties
import DaggerModelsPartII.JTFrameProjection

/-!
# The actual rigidified JT cosimplicial frame

The full outer-natural Reedy frame is augmented to the rigidified reversal
simplex. Its zero component is the chosen canonical isomorphism, and the
augmentation is componentwise a literal dagger DK weak equivalence.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite Simplicial MorphismProperty
open DaggerModels DaggerModels.PartII.RigidifiedJTFrames
open DaggerModels.PartII.JTRelativeReedyFrame

namespace DaggerModels.PartII.JTActualCosimplicialFrame

noncomputable section

private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance

/-- The constant outer diagram of rigidified reversal simplices, with the
ordinary simplex index as its source. -/
def constantA : SimplexCategory ⥤ OuterDiagram :=
  (Functor.curry.obj
    (CategoryTheory.Prod.fst ReverseSimplex SimplexCategory ⋙ A)).flip

/-- The literal augmentation of the represented generators, curried with
the ordinary simplex index first. -/
def XiAugmentationCurried : XiCurried ⟶ constantA :=
  (flipFunctor ReverseSimplex SimplexCategory Coefficient).map
    (Functor.curry.map JTFrameProjection.XiAugmentation)

/-- The actual full-outer cosimplicial frame augmentation. -/
def augmentation : Gamma ⟶ constantA :=
  comparison ≫ XiAugmentationCurried

/-- The same augmentation with the reversal-simplex index outermost. -/
def augmentationOuter : GammaOuter ⟶ constantA.flip :=
  (flipFunctor SimplexCategory ReverseSimplex Coefficient).map augmentation

/-- The prescribed zero-degree identification of the actual frame. -/
def GammaZeroIso : Gamma.obj ⦋0⦌ ≅ A := by
  change XiCurried.obj ⦋0⦌ ≅ A
  exact XiZeroIso

/-- The augmentation is exactly the prescribed zero identification. -/
theorem augmentation_zero :
    augmentation.app ⦋0⦌ = GammaZeroIso.hom := by
  ext m
  change (comparison.app ⦋0⦌).app m ≫
    JTFrameProjection.XiAugmentation.app (m, ⦋0⦌) =
      XiZeroIso.hom.app m
  simpa only [comparison_zero, NatTrans.id_app, Category.id_comp] using
    JTFrameProjection.XiAugmentation_zero m

/-- Every component of the actual frame augmentation is a weak
equivalence in the original global dagger simplicial-category model. -/
theorem augmentation_component_weak (m : ReverseSimplex) (n : ℕ) :
    weakEquivalences Coefficient ((augmentation.app ⦋n⦌).app m) := by
  change weakEquivalences Coefficient
    ((comparison.app ⦋n⦌).app m ≫
      JTFrameProjection.XiAugmentation.app (m, ⦋n⦌))
  exact (weakEquivalences Coefficient).comp_mem _ _
    (comparison_component_weak m n)
    (JTFrameProjection.XiAugmentation_weak m ⦋n⦌)

/-- The same component belongs to the literal dagger DK class. -/
theorem augmentation_component_daggerDK (m : ReverseSimplex) (n : ℕ) :
    DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement
      ((augmentation.app ⦋n⦌).app m) := by
  rw [← DaggerActualRigidificationQuillen.target_weak]
  exact augmentation_component_weak m n

/-- Every ordinary-simplex map of the actual frame is a weak equivalence
at each reversal-simplex index. -/
theorem GammaOuter_map_weak (m : ReverseSimplex)
    {j k : SimplexCategory} (θ : j ⟶ k) :
    weakEquivalences Coefficient ((GammaOuter.obj m).map θ) := by
  let W := weakEquivalences Coefficient
  have hc : (constantA.map θ).app m = 𝟙 _ := by
    simp [constantA]
  have hn := congrArg (fun τ : Gamma.obj j ⟶ constantA.obj k ↦ τ.app m)
    (augmentation.naturality θ)
  change (GammaOuter.obj m).map θ ≫ (augmentation.app k).app m =
    (augmentation.app j).app m ≫ (constantA.map θ).app m at hn
  rw [hc, Category.comp_id] at hn
  have hj : W ((augmentation.app j).app m) := by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, ⦋n⦌ = j :=
      ⟨j.len, SimplexCategory.ext _ _ rfl⟩
    exact augmentation_component_weak m n
  have hk : W ((augmentation.app k).app m) := by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, ⦋n⦌ = k :=
      ⟨k.len, SimplexCategory.ext _ _ rfl⟩
    exact augmentation_component_weak m n
  have hcomp : W ((GammaOuter.obj m).map θ ≫ (augmentation.app k).app m) := by
    rw [hn]
    exact hj
  exact W.of_postcomp _ _ hk hcomp

/-- The opposite actual frame is homotopically constant in the precise
sense that all simplex-index maps are weak equivalences. -/
theorem GammaOuter_op_map_weak (m : ReverseSimplex)
    {j k : SimplexCategoryᵒᵖ} (θ : j ⟶ k) :
    weakEquivalences Coefficientᵒᵖ (((GammaOuter.obj m).op).map θ) := by
  rw [weakEquivalences_op]
  change weakEquivalences Coefficient ((GammaOuter.obj m).map θ.unop)
  exact GammaOuter_map_weak m θ.unop

end

end DaggerModels.PartII.JTActualCosimplicialFrame
