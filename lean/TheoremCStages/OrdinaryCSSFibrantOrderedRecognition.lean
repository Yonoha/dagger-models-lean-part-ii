import RawOrdinaryJTChosenMapCalibration
import OrdinaryCSSConditions
import DaggerModelsPartII.DiagonalRecognition

/-!
# Ordered chosen fibers between actual ordinary CSS fibrant objects

A weak map between two fibrant objects of the original ordinary CSS
localization is weak in the injective Kan base model. Its literal degree-zero
and degree-one rows are therefore weak, and the unchanged ordered chosen
fiber map is weak at every original pair of vertices.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCSSFibrantOrderedRecognition

open OrdinaryCSSLocalization (Space)

noncomputable section

private abbrev N := InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
private abbrev C := OrdinaryCSSLocalization.model

/-- A weak map between actual CSS fibrant objects is weak in the original
injective Kan diagram model, with neither model structure left implicit. -/
theorem cssWeak_baseWeak {W Z : Space} (f : W ⟶ Z)
    (hW : @IsFibrant Space _ C.categoryWithFibrations _ W)
    (hZ : @IsFibrant Space _ C.categoryWithFibrations _ Z)
    (hf : C.categoryWithWeakEquivalences.weakEquivalences f) :
    N.categoryWithWeakEquivalences.weakEquivalences f := by
  letI : ModelCategory Space := N
  have hLW := (OrdinaryCSSLocalization.isFibrant_iff W).mp hW
  have hLZ := (OrdinaryCSSLocalization.isFibrant_iff Z).mp hZ
  have hlocal : Localization.localEquivalences
      OrdinaryCSSLocalization.localizingFamily f := by
    simpa only [OrdinaryCSSLocalization.exactClasses.2] using hf
  change weakEquivalences Space f
  exact (Localization.localEquivalence_iff_weak_of_local
    OrdinaryCSSLocalization.localizingFamily f hLW hLZ).mp hlocal

/-- The original ordered chosen map is weak at every literal pair of
vertices when the actual CSS map and both its objects are fibrant. -/
theorem cssWeak_chosenMappingMap_weak {W Z : Space} (f : W ⟶ Z)
    (hW : @IsFibrant Space _ C.categoryWithFibrations _ W)
    (hZ : @IsFibrant Space _ C.categoryWithFibrations _ Z)
    (hf : C.categoryWithWeakEquivalences.weakEquivalences f)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (RawOrdinaryJTChosenMapCalibration.chosenMappingMap f x y) := by
  letI : ModelCategory Space := N
  haveI : IsFibrant W := ((OrdinaryCSSLocalization.isFibrant_iff W).mp hW).1
  haveI : IsFibrant Z := ((OrdinaryCSSLocalization.isFibrant_iff Z).mp hZ).1
  have hbase := cssWeak_baseWeak f hW hZ hf
  change weakEquivalences Space f at hbase
  rw [InjectiveKanDiagram.model_weakEquivalences] at hbase
  haveI : WeakEquivalence (f.app (op ⦋0⦌)) :=
    (weakEquivalence_iff _).mpr (hbase (op ⦋0⦌))
  haveI : WeakEquivalence (f.app (op ⦋1⦌)) :=
    (weakEquivalence_iff _).mpr (hbase (op ⦋1⦌))
  haveI : IsFibrant (W.obj (op ⦋0⦌)) :=
    OrdinarySegalWalkingEvaluation.row_isFibrant W 0
  haveI : IsFibrant (Z.obj (op ⦋0⦌)) :=
    OrdinarySegalWalkingEvaluation.row_isFibrant Z 0
  haveI : WeakEquivalence (OrdinarySegalOrderedMappingMaps.endpointMap f) := by
    change WeakEquivalence (prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)))
    exact DiagonalRecognition.prodMap_weak (f.app (op ⦋0⦌))
  exact DiagonalRecognition.chosenMap_weak_of_weak_square
    (OrdinarySegalOrderedMappingFibres.endpointArrow W)
    (OrdinarySegalOrderedMappingFibres.endpointArrow Z)
    (f.app (op ⦋1⦌))
    (OrdinarySegalOrderedMappingMaps.endpointMap f)
    (OrdinarySegalOrderedMappingMaps.endpoint_naturality f)
    (OrdinarySegalOrderedMappingFibres.endpointPoint W x y)
    (OrdinarySegalOrderedMappingFibres.endpointPoint Z
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌) y))
    (OrdinarySegalOrderedMappingMaps.point_naturality f x y)

#print axioms cssWeak_baseWeak
#print axioms cssWeak_chosenMappingMap_weak

end
end DaggerModels.PartII.OrdinaryCSSFibrantOrderedRecognition
