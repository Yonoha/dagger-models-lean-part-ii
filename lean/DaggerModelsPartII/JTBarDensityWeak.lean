import DaggerModelsPartII.JTRealizationDiagonal
import DaggerModelsPartII.OrdinaryRigidifiedDiagonalWeak
import DaggerModelsPartII.JTBarDensityEssentialSurj
import DaggerModelsPartII.JTProjectiveComparisonWeak
import DaggerModelsPartII.JTBarComparison

/-!
# The original natural JT bar density comparison

The actual JT realization preserves rowwise Kan weak equivalences after
ordinary rigidification, by its natural diagonal identification and the
original rigidified diagonal theorem. Applied to the original augmentation,
the independent coherent object witness supplies the dagger DK condition.
The original capital comparison at the bar and fixed collapse then prove
weakness of the prescribed beta, retaining its strict transport identity.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open DaggerUnitaryInvariance
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryDwyerKanCore

namespace DaggerModels.PartII.JTBarDensityWeak

open OrdinaryJTRealization JTReversalInput JTRealizationDiagonal
open JTGroupoidWeightWeak JTProjectiveBar JTBarComparison
open OrdinaryRigidification.DaggerRigidification

noncomputable section

private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- Rowwise Kan weakness is preserved by the literal original JT
realization after the original ordinary rigidification. -/
theorem realization_map_W {W V : BiPresheaf} (f : W ⟶ V)
    (hf : ∀ m : SimplexCategory,
      DaggerSSetGluing.GW ((ordinaryCurry.map f).app (op m))) :
    OrdinaryDwyerKanCore.W (rigidification.map (realization.map f)) := by
  have hrow : ∀ n : ℕ,
      OrdinaryDwyerKanCore.W
        (rigidification.map ((rowwiseJ.map f).app (op ⦋n⦌))) := by
    intro n
    rw [rowwiseJ_map_app]
    exact rigidification_jRealization_map_W _ (hf ⦋n⦌)
  have hdiag := OrdinaryRigidifiedDiagonalWeak.diagonal_W (rowwiseJ.map f) hrow
  let e := realizationDiagonalIso
  let ea : Arrow.mk (rigidification.map (realization.map f)) ≅
      Arrow.mk (rigidification.map
        (DaggerNativeBisimplicialDiagonal.diagonalFunctor.map (rowwiseJ.map f))) :=
    Arrow.isoMk (rigidification.mapIso (e.app W)) (rigidification.mapIso (e.app V))
      (by
        change rigidification.map (e.app W).hom ≫
            rigidification.map
              (DaggerNativeBisimplicialDiagonal.diagonalFunctor.map (rowwiseJ.map f)) =
          rigidification.map (realization.map f) ≫ rigidification.map (e.app V).hom
        rw [← rigidification.map_comp, ← rigidification.map_comp]
        exact congrArg rigidification.map (e.hom.naturality f).symm)
  exact (OrdinaryDwyerKanCore.W.arrow_mk_iso_iff ea).2 hdiag

private def rowRestrictionIso (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (m : SimplexCategory) :
    (ordinaryCurry.obj (ordinaryInput.obj W)).obj (op m) ≅
      W.obj (op (ReverseSimplex.inclusion.obj m)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    dsimp [ordinaryCurry, ordinaryInput]
    simp)

open scoped SSet.modelCategoryQuillen in
/-- The exact middle density factor is ordinary DK after forgetting
dagger; the augmentation and both realizations are the prescribed maps. -/
theorem realized_barAugmentation_W (X : DaggerSSet.{0}) :
    OrdinaryDwyerKanCore.W
      (DaggerSimplicialCat.forget.map
        (daggerRigidification.map
          (DaggerJTRealization.daggerRealization.map (barAugmentation.app X)))) := by
  change OrdinaryDwyerKanCore.W
    (rigidification.map (realization.map (ordinaryInput.map (barAugmentation.app X))))
  apply realization_map_W
  intro m
  let ea : Arrow.mk
      ((ordinaryCurry.map (ordinaryInput.map (barAugmentation.app X))).app (op m)) ≅
      Arrow.mk ((barAugmentation.app X).app (op (ReverseSimplex.inclusion.obj m))) :=
    Arrow.isoMk
    (rowRestrictionIso (barOnDagger.obj X) m)
    (rowRestrictionIso (ConstantVertexAdjunction.delta.obj X) m)
    (show _ = _ by ext k x; rfl)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).1
  rw [weakEquivalence_iff]
  apply ((weakEquivalences SSet.{0}).arrow_mk_iso_iff ea).2
  rw [← weakEquivalence_iff]
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2
    (barAugmentation_rowwise_GW X (op (ReverseSimplex.inclusion.obj m)))

/-- Local weakness and the separately proved coherent object condition
give dagger DK for the literal realized augmentation. -/
theorem realized_barAugmentation_daggerDK (X : DaggerSSet.{0}) :
    DaggerGlobalDK.daggerDK standardReplacement
      (daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map (barAugmentation.app X))) :=
  ⟨(realized_barAugmentation_W X).1,
    JTBarDensityEssentialSurj.rigidified_barAugmentation_coherentlyEssentiallySurjective X⟩

/-- The prescribed natural beta is dagger DK, with no target projective
cofibrancy hypothesis and no replacement of the original augmentation. -/
theorem beta_daggerDK (X : DaggerSSet.{0}) :
    DaggerGlobalDK.daggerDK standardReplacement (beta.app X) := by
  rw [← DaggerActualRigidificationQuillen.target_weak]
  let P := weakEquivalences DaggerSimplicialCat.{0, 0}
  have hLambda : P (JTCoendComparison.comparison.app (barOnDagger.obj X)) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0} _
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact JTProjectiveComparisonWeak.comparison_bar_daggerDK X
  have hMiddle : P (daggerRigidification.map
      (DaggerJTRealization.daggerRealization.map (barAugmentation.app X))) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0} _
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact realized_barAugmentation_daggerDK X
  rw [beta_app]
  exact P.comp_mem _ _ hLambda
    (P.comp_mem _ _ hMiddle (P.of_isIso (constantCollapse.hom.app X)))

/-- The actual frame realization of the original augmentation is weak. -/
theorem frameRealization_barAugmentation_weak (X : DaggerSSet.{0}) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (JTFrameAdjunction.frameRealization.map (barAugmentation.app X)) := by
  apply (beta_weak_iff X).1
  rw [DaggerActualRigidificationQuillen.target_weak]
  exact beta_daggerDK X

end

end DaggerModels.PartII.JTBarDensityWeak
