import DaggerModelsPartII.DiagramMappingLimits
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-! Strict diagram mapping spaces send pushout squares to pullback squares. -/

set_option autoImplicit false

open CategoryTheory Limits

universe u v

namespace DaggerModels.PartII

variable {C : Type u} [Category.{v} C]

/-- Mapping a diagram pushout into a fixed target gives a pullback of mapping spaces. -/
theorem diagramMappingSpace_isPullback
    {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r) (W : C ⥤ SSet.{u}) :
    IsPullback (diagramMappingPrecomp l W) (diagramMappingPrecomp r W)
      (diagramMappingPrecomp i W) (diagramMappingPrecomp k W) := by
  letI : PreservesLimitsOfShape WalkingCospan (diagramMappingSource W) :=
    diagramMappingSource_preservesLimitsOfShape WalkingCospan W
  exact (sq.op.map (diagramMappingSource W)).flip

end DaggerModels.PartII
