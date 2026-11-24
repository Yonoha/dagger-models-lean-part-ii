import RawOrdinaryJTChosenMapCalibration
import OrdinarySegalVerticalPrecompletionDerivedUnit
import DaggerModelsPartII.DiagonalRecognition
import OriginalSimplicialTrivialFibrationTensor
import SSetProductGeometric
import NativeAllCofibrantLocalizationSaturation

/-!
# The corrected unit followed by a rowwise replacement on chosen fibers

The chosen map is the literal ordered mapping-fiber map of the composite
`unit W ≫ i`. The intermediate corrected precompletion is not assumed
injectively fibrant. Composition is calibrated after the actual Kan
localization, where the chosen comparison lifts are functorial.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCompletedUnitChosenMap

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingMaps (endpointMap endpoint_naturality point_naturality)
open RawOrdinaryJTChosenMapCalibration (chosenMappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev P (W : Space) :=
  OrdinarySegalVerticalPrecompletion.precompletion W

/-- The actual Cartesian product of two arbitrary Kan weak equivalences is
weak, without a fibrancy premise on any of the four simplicial sets. -/
theorem prodMap_weak {A B C D : SSet.{0}} (f : A ⟶ B) (g : C ⟶ D)
    [WeakEquivalence f] [WeakEquivalence g] :
    WeakEquivalence (prod.map f g) := by
  have ht : WeakEquivalence (f ⊗ₘ g) :=
    (DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mp
      (DaggerSSetProductGeometric.tensorMap_geometric f g
        ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence f).mpr inferInstance)
        ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence g).mpr inferInstance))
  letI := ht
  have h : (f ⊗ₘ g) ≫
      (DaggerOriginalSimplicialTrivialFibrationTensor.tensorProductIso B D).hom =
    (DaggerOriginalSimplicialTrivialFibrationTensor.tensorProductIso A C).hom ≫
      prod.map f g :=
    DaggerOriginalSimplicialTrivialFibrationTensor.tensorProductIso_natural f g
  have hc : WeakEquivalence
      ((DaggerOriginalSimplicialTrivialFibrationTensor.tensorProductIso A C).hom ≫
        prod.map f g) := by
    rw [← h]
    infer_instance
  letI := hc
  exact weakEquivalence_of_precomp
    (DaggerOriginalSimplicialTrivialFibrationTensor.tensorProductIso A C).hom
    (prod.map f g)

/-- A rowwise weak map acts weakly on the literal chosen ordered fibers,
including when its source ordinary simplicial space is not fibrant. -/
theorem replacementChosenMap_weak {X R : Space} (i : X ⟶ R)
    (hi : ∀ q : SimplexCategoryᵒᵖ, WeakEquivalence (i.app q))
    (x y : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (chosenMappingMap i x y) := by
  haveI : WeakEquivalence (i.app (op ⦋1⦌)) := hi (op ⦋1⦌)
  haveI : WeakEquivalence (endpointMap i) := by
    change WeakEquivalence (prod.map (i.app (op ⦋0⦌)) (i.app (op ⦋0⦌)))
    letI : WeakEquivalence (i.app (op ⦋0⦌)) := hi (op ⦋0⦌)
    exact prodMap_weak _ _
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

/-- The exact ordered chosen maps compose after Kan localization, with
the original ordered pair and the actual intermediate image pair. -/
theorem chosenMappingMap_comp {U V T : Space} (f : U ⟶ V) (g : V ⟶ T)
    (x y : (U.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (weakEquivalences SSet.{0}).Q.map (chosenMappingMap f x y) ≫
        (weakEquivalences SSet.{0}).Q.map
          (chosenMappingMap g
            ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
            ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y)) =
      (weakEquivalences SSet.{0}).Q.map (chosenMappingMap (f ≫ g) x y) := by
  have h := ChosenHomotopyFiberFunctor.chosenMap_comp
    (endpointArrow U) (endpointArrow V) (endpointArrow T)
    (f.app (op ⦋1⦌)) (endpointMap f) (endpoint_naturality f)
    (g.app (op ⦋1⦌)) (endpointMap g) (endpoint_naturality g)
    (endpointPoint U x y)
    (endpointPoint V ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y))
    (endpointPoint T (((f ≫ g).app (op ⦋0⦌)).app (op ⦋0⦌) x)
      (((f ≫ g).app (op ⦋0⦌)).app (op ⦋0⦌) y))
    (point_naturality f x y)
    (point_naturality g
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y))
  simpa only [chosenMappingMap, endpointMap, NatTrans.comp_app,
    prod.map_map, Function.comp_apply] using h

/-- The literal chosen map of the completed unit is weak at every pair of
original vertices. Neither completeness nor fibrancy of `P W` is used. -/
theorem completedUnitChosenMap_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (R : Space) (i : P W ⟶ R)
    (hi : ∀ q : SimplexCategoryᵒᵖ, WeakEquivalence (i.app q))
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (chosenMappingMap (OrdinarySegalVerticalPrecompletion.unit W ≫ i) x y) := by
  let u := OrdinarySegalVerticalPrecompletion.unit W
  let Q := (weakEquivalences SSet.{0}).Q
  have hu : WeakEquivalence (chosenMappingMap u x y) := by
    change WeakEquivalence
      (OrdinarySegalVerticalPrecompletionDerivedUnit.unitChosenMap W x y)
    exact OrdinarySegalVerticalPrecompletionDerivedUnit.unitChosenMap_weak
      W hSegal x y
  have hv : WeakEquivalence
      (chosenMappingMap i
        ((u.app (op ⦋0⦌)).app (op ⦋0⦌) x)
        ((u.app (op ⦋0⦌)).app (op ⦋0⦌) y)) :=
    replacementChosenMap_weak i hi _ _
  have hcomp := chosenMappingMap_comp u i x y
  haveI : IsIso (Q.map (chosenMappingMap u x y)) :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      Q _).mp hu
  haveI : IsIso (Q.map (chosenMappingMap i
      ((u.app (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((u.app (op ⦋0⦌)).app (op ⦋0⦌) y))) :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      Q _).mp hv
  have hIso : IsIso (Q.map (chosenMappingMap (u ≫ i) x y)) := by
    rw [← hcomp]
    infer_instance
  exact (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q _).mpr hIso

#print axioms prodMap_weak
#print axioms replacementChosenMap_weak
#print axioms chosenMappingMap_comp
#print axioms completedUnitChosenMap_weak

end

end DaggerModels.PartII.OrdinaryCompletedUnitChosenMap
