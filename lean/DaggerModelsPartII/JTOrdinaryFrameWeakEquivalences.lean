import DaggerModelsPartII.DaggerOrdinaryDwyerKan
import DaggerModelsPartII.OrdinaryDwyerKanClosure
import DaggerModelsPartII.JTActualCosimplicialFrame
import DaggerModelsPartII.JTXiOrdinaryLatching
import DaggerModelsPartII.JTForgottenFrameCofibrancy

/-!
# Ordinary DK inputs of the literal JT frames

Apply the checked comparison of the two retained component categories to the
actual Gamma/Xi augmentations and the prescribed comparison. Their ordinary
latching cofibrations are reused. These statements do not install an ordinary
model structure or assert homotopical invariance of arbitrary realizations.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Simplicial DaggerModels
open DaggerModels.DaggerOrdinaryDwyerKan DaggerModels.OrdinaryDwyerKanCore
open DaggerModels.PartII.RigidifiedJTFrames DaggerModels.PartII.JTRelativeReedyFrame

namespace DaggerModels.PartII.JTOrdinaryFrameWeakEquivalences

noncomputable section

private local instance : Limits.HasColimits SimplicialCat.{0, 0} := simplicialCatHasColimits
private local instance : Limits.HasLimits SimplicialCat.{0, 0}ᵒᵖ := inferInstance

private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- Each literal Gamma augmentation is ordinary DK after forgetting dagger. -/
theorem gamma_augmentation_W (m : ReverseSimplex) (n : ℕ) :
    W (DaggerSimplicialCat.forget.map
      ((JTActualCosimplicialFrame.augmentation.app ⦋n⦌).app m)) :=
  daggerDK_forget_W DaggerUnitaryInvariance.standardReplacement _
    (JTActualCosimplicialFrame.augmentation_component_daggerDK m n)

/-- The actual Xi augmentation, including its prescribed zero-stage identification,
is ordinary DK after forgetting dagger. -/
theorem xi_augmentation_W (m : ReverseSimplex) (k : SimplexCategory) :
    W (DaggerSimplicialCat.forget.map (JTFrameProjection.XiAugmentation.app (m, k))) := by
  apply daggerDK_forget_W DaggerUnitaryInvariance.standardReplacement
  rw [← DaggerActualRigidificationQuillen.target_weak]
  exact JTFrameProjection.XiAugmentation_weak m k

/-- The actual represented frame comparison is ordinary DK, without changing
its lower-case comparison component or either endpoint. -/
theorem comparison_W (m : ReverseSimplex) (n : ℕ) :
    W (DaggerSimplicialCat.forget.map ((comparison.app ⦋n⦌).app m)) :=
  daggerDK_forget_W DaggerUnitaryInvariance.standardReplacement _
    (comparison_component_daggerDK m n)

/-- The original Gamma frame remains homotopically constant for the retained
ordinary DK class after forgetting dagger. -/
theorem gamma_map_W (m : ReverseSimplex) {j k : SimplexCategory} (θ : j ⟶ k) :
    W ((GammaOuter.obj m ⋙ DaggerSimplicialCat.forget).map θ) := by
  apply daggerDK_forget_W DaggerUnitaryInvariance.standardReplacement
  rw [← DaggerActualRigidificationQuillen.target_weak]
  exact JTActualCosimplicialFrame.GammaOuter_map_weak m θ

/-- The actual Xi augmentation square gives ordinary DK of each original
simplex-index map, by the proved ordinary two-of-three property. -/
theorem xi_map_W (m : ReverseSimplex) {j k : SimplexCategory} (θ : j ⟶ k) :
    W ((JTXiOrdinaryLatching.actualOrdinaryXi m).map θ) := by
  let F := DaggerSimplicialCat.forget.{0, 0}
  let p : (m, j) ⟶ (m, k) := (𝟙 m, θ)
  have hconst : (CategoryTheory.Prod.fst ReverseSimplex SimplexCategory ⋙ A).map p =
      𝟙 (A.obj m) := by
    change A.map (𝟙 m) = _
    exact A.map_id m
  have hsquare := congrArg F.map (JTFrameProjection.XiAugmentation.naturality p)
  simp only [CategoryTheory.Functor.map_comp, hconst] at hsquare
  apply W.of_postcomp _ _ (xi_augmentation_W m k)
  change W (F.map (Xi.map p) ≫ F.map (JTFrameProjection.XiAugmentation.app (m, k)))
  rw [hsquare]
  have hFid : F.map (𝟙 (A.obj m)) = 𝟙 (F.obj (A.obj m)) := F.map_id _
  rw [hFid]
  exact W.comp_mem _ _ (xi_augmentation_W m j) (W.id_mem _)

/-- All checked ordinary Gamma frame inputs, for the same actual augmentation,
original matching/latching map and native DK class. No model instance is assumed. -/
theorem gamma_frame_inputs (m : ReverseSimplex) :
    (∀ n : ℕ, DaggerOrdinaryRigidificationCof.ordinaryCofibrations
      (((matchingComparison n).app
        ((GammaOuter.obj m ⋙ DaggerSimplicialCat.forget).op)).unop)) ∧
    (∀ n : ℕ, W (DaggerSimplicialCat.forget.map
      ((JTActualCosimplicialFrame.augmentation.app ⦋n⦌).app m))) ∧
    (∀ {j k : SimplexCategory} (θ : j ⟶ k),
      W ((GammaOuter.obj m ⋙ DaggerSimplicialCat.forget).map θ)) :=
  ⟨JTForgottenFrameCofibrancy.forgotten_Gamma_ordinary_matching_cofibration m,
    gamma_augmentation_W m, gamma_map_W m⟩

/-- All checked ordinary Xi frame inputs, retaining its original full-index
section and prescribed augmentation. No ordinary model structure is asserted. -/
theorem xi_frame_inputs (m : ReverseSimplex) :
    (∀ n : ℕ, DaggerOrdinaryRigidificationCof.ordinaryCofibrations
      (((matchingComparison n).app (JTXiOrdinaryLatching.actualOrdinaryXi m).op).unop)) ∧
    (∀ k : SimplexCategory,
      W (DaggerSimplicialCat.forget.map (JTFrameProjection.XiAugmentation.app (m, k)))) ∧
    (∀ {j k : SimplexCategory} (θ : j ⟶ k),
      W ((JTXiOrdinaryLatching.actualOrdinaryXi m).map θ)) :=
  ⟨JTXiOrdinaryLatching.actualOrdinaryXi_matching_cofibration m,
    xi_augmentation_W m, xi_map_W m⟩

end

end DaggerModels.PartII.JTOrdinaryFrameWeakEquivalences
