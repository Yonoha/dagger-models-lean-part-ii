import DaggerModelsPartII.JTBarDensityWeak
import DaggerModelsPartII.JTProjectiveOrderedFiberComparison
import DaggerModelsPartII.JTGtildeGeneratorFiberCalibration

/-!
# The actual projective replacement under ordinary JT realization

The ordinary rigidification of the literal map induced by `p : Qproj W ⟶ W`
is DK weak for every `W`. Its original Hom maps are Kan weak. The generator
equation retains both indices and the actual projective replacement map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTProjectiveRealizationMappingWeak

open OrdinaryJTRealization JTReversalInput JTStrictificationMaps
open JTRealizationDiagonal JTProjectiveOrderedFiberComparison

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The original two-index ordinary map of the actual projective replacement. -/
def ordinaryP (W : Source) :
    ordinaryInput.obj (Qproj.obj W) ⟶ ordinaryInput.obj W :=
  ordinaryInput.map (p.app W)

/-- The literal realization of the original projective replacement map. -/
def realizedP (W : Source) :
    realization.obj (ordinaryInput.obj (Qproj.obj W)) ⟶
      realization.obj (ordinaryInput.obj W) :=
  realization.map (ordinaryP W)

/-- Each actual curry row is the checked projective row map. -/
theorem ordinaryP_row (W : Source) (m : SimplexCategory) :
    (ordinaryCurry.map (ordinaryP W)).app (op m) = pRow W m := rfl

/-- The original ordinary rigidification of the literal projective map is DK weak. -/
theorem rigidified_realizedP_W (W : Source) :
    OrdinaryDwyerKanCore.W (rigidification.map (realizedP W)) := by
  apply JTBarDensityWeak.realization_map_W
  intro m
  rw [ordinaryP_row]
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    ((mem_trivialFibrations_iff _).1 (pRow_trivialFibration W m)).2

/-- Every original rigidified Hom of the actual projective map is Kan weak. -/
theorem rigidified_realizedP_hom_weak (W : Source)
    (a b : (rigidification.obj
      (realization.obj (ordinaryInput.obj (Qproj.obj W)))).Obj) :
    WeakEquivalence ((rigidification.map (realizedP W)).map a b) :=
  (OrdinaryDwyerKanCore.localGeometric_iff_native _).1
    (rigidified_realizedP_W W).1 a b

/-- The literal generator action of `p` at both original indices. -/
theorem realizedP_generator (W : Source) (q : Index)
    (w : (ordinaryInput.obj (Qproj.obj W)).obj (op q)) :
    JTRealizationGenerators.generator (ordinaryInput.obj (Qproj.obj W)) q w ≫
      realizedP W =
    JTRealizationGenerators.generator (ordinaryInput.obj W) q
      ((ordinaryP W).app (op q) w) :=
  JTRealizationGenerators.generator_naturality (ordinaryP W) q w

/-- The zero generator in the raw diagram, with the same terminal section. -/
def rawZeroGeneratorVertex (W : Source)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (realization.obj (ordinaryInput.obj W)).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv
    (JTGtildeOrderedFiberAction.zeroTensorVertex ≫
      JTRealizationGenerators.generator (ordinaryInput.obj W) (⦋0⦌, ⦋0⦌) z)

/-- The actual projective map sends the chosen zero generator to the raw one. -/
theorem realizedP_zeroGeneratorVertex (W : Source)
    (x : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (realizedP W).app (op ⦋0⦌)
        (JTGtildeGeneratorFiberCalibration.zeroGeneratorVertex W x) =
      rawZeroGeneratorVertex W ((pRow W ⦋0⦌).app (op ⦋0⦌) x) := by
  change SSet.yonedaEquiv
      ((JTGtildeOrderedFiberAction.zeroTensorVertex ≫
        JTRealizationGenerators.generator
          (ordinaryInput.obj (Qproj.obj W)) (⦋0⦌, ⦋0⦌) x) ≫
          realizedP W) =
    SSet.yonedaEquiv
      (JTGtildeOrderedFiberAction.zeroTensorVertex ≫
        JTRealizationGenerators.generator (ordinaryInput.obj W) (⦋0⦌, ⦋0⦌)
          ((pRow W ⦋0⦌).app (op ⦋0⦌) x))
  rw [Category.assoc, realizedP_generator]
  rfl

end

end DaggerModels.PartII.JTProjectiveRealizationMappingWeak
