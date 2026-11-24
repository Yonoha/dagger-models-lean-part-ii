import DaggerModelsPartII.JTFrameAugmentation
import DaggerModelsPartII.RigidifiedJTFrames
import DaggerModelsPartII.JTParameterZero
import OriginalSimplicialTrivialFibrationTensor
import ActualNerveTrivialFibrationRigidification

/-!
# The actual JT frame projection

This draft uses the original Kan trivial-fibration structure on the groupoid
simplex parameter.  No ordinary Joyal model or rigidification Quillen theorem
is required for the special projection.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFrameProjection

open DaggerJTAdjunction DaggerJTFrameUnderlying JTFrameAugmentation
open JTFrameZero RigidifiedJTFrames GroupoidSimplex JTParameterZero
open DaggerOriginalSimplicialTrivialFibrationTensor

noncomputable section

/-- The actual map from a groupoid-completed simplex to its zero-stage value
is a Kan trivial fibration. -/
theorem parameter_projection_trivialFibration (k : SimplexCategory) :
    trivialFibrations SSet.{0}
      (parameter.map (SimplexCategory.isTerminalZero.from k)) := by
  let P := trivialFibrations SSet.{0}
  let q := parameter.map (SimplexCategory.isTerminalZero.from k)
  let e : parameter.obj ⦋0⦌ ≅ (⊤_ SSet.{0}) :=
    parameterZeroIsTerminal.uniqueUpToIso terminalIsTerminal
  have hterminal : q ≫ e.hom = terminal.from (parameter.obj k) :=
    terminalIsTerminal.hom_ext _ _
  have hqe : P (q ≫ e.hom) := by
    rw [hterminal]
    exact augmentation_trivialFibration k
  have hqei : P ((q ≫ e.hom) ≫ e.inv) :=
    P.comp_mem _ _ hqe (P.of_isIso e.inv)
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hqei

/-- After forgetting dagger, the represented frame projection is a Kan
trivial fibration. -/
theorem frame_projection_trivialFibration (m : ReverseSimplex)
    (k : SimplexCategory) :
    trivialFibrations SSet.{0}
      ((frame.map (projectionToZero.app (m, k))).hom) := by
  let P := trivialFibrations SSet.{0}
  let u := projectionToZero.app (m, k)
  let q := parameter.map (SimplexCategory.isTerminalZero.from k)
  have hq : P q := parameter_projection_trivialFibration k
  have hparameter : P (frameParameter.map u) := by
    change P ((underlyingSimplex.map (𝟙 m)) ⊗ₘ q)
    simpa only [Functor.map_id] using
      (tensorHom_trivialFibration (𝟙 (underlyingSimplex.obj m)) q
        (P.of_isIso _) hq)
  let e : Arrow.mk ((frame.map u).hom) ≅ Arrow.mk (frameParameter.map u) :=
    Arrow.isoMk (frameUnderlyingIso.app (m, k))
      (frameUnderlyingIso.app (m, ⦋0⦌))
      (frameUnderlyingIso.hom.naturality u).symm
  exact (P.arrow_mk_iso_iff e).2 hparameter

/-- The literal rigidified frame projection is a dagger DK equivalence. -/
theorem Xi_projection_daggerDK (m : ReverseSimplex)
    (k : SimplexCategory) :
    DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement
      (Xi.map (projectionToZero.app (m, k))) := by
  let f := (frame.map (projectionToZero.app (m, k))).hom
  obtain ⟨hf, hw⟩ :=
    (mem_trivialFibrations_iff f).1 (frame_projection_trivialFibration m k)
  letI : Fibration f := hf
  letI : WeakEquivalence f := hw
  obtain ⟨hlocal, hsurj⟩ :=
    DaggerActualNerveTrivialFibrationRigidification.trivialFibration_local_and_surjective f
  exact DaggerGlobalDK.daggerDK_of_surjective_local
    DaggerUnitaryInvariance.standardReplacement _ hsurj hlocal

/-- The actual frame augmentation after applying the original dagger
rigidification, with the original zero-stage target. -/
def XiAugmentation :
    Xi ⟶
      CategoryTheory.Prod.fst ReverseSimplex SimplexCategory ⋙ A :=
  Functor.whiskerRight frameAugmentation
      OrdinaryRigidification.DaggerRigidification.daggerRigidification ≫
    (Functor.associator _ _ _).hom

/-- The augmentation component is exactly the rigidified projection followed
by the chosen degree-zero identification. -/
theorem XiAugmentation_app (m : ReverseSimplex) (k : SimplexCategory) :
    XiAugmentation.app (m, k) =
      Xi.map (projectionToZero.app (m, k)) ≫ XiZeroIso.hom.app m := by
  simp [XiAugmentation, frameAugmentation, XiZeroIso, Xi, A,
    Category.assoc]

/-- The augmentation agrees with the chosen normalization at degree zero. -/
theorem XiAugmentation_zero (m : ReverseSimplex) :
    XiAugmentation.app (m, ⦋0⦌) = XiZeroIso.hom.app m := by
  rw [XiAugmentation_app, projectionToZero_zero]
  simp

local instance actualGlobalModel : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- Each component of the literal rigidified JT augmentation is an actual
weak equivalence in the original global dagger DK model. -/
theorem XiAugmentation_weak (m : ReverseSimplex) (k : SimplexCategory) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (XiAugmentation.app (m, k)) := by
  let W := weakEquivalences DaggerSimplicialCat.{0, 0}
  have hprojection : W (Xi.map (projectionToZero.app (m, k))) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0}
      (Xi.map (projectionToZero.app (m, k)))
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact Xi_projection_daggerDK m k
  have hzero : W (XiZeroIso.hom.app m) := W.of_isIso _
  rw [XiAugmentation_app]
  exact W.comp_mem _ _ hprojection hzero

end

end DaggerModels.PartII.JTFrameProjection
