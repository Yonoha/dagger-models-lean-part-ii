import DaggerModelsPartII.DiagramMappingSpace
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! The tensor–mapping adjunction for the literal mapping spaces of diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory

universe u v

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]

/-- Covariant functoriality in the target of the diagram mapping space. -/
def diagramMappingTarget (A : C ⥤ SSet.{u}) : (C ⥤ SSet.{u}) ⥤ SSet.{u} :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (SSet.stdSimplex.{u} ⋙ diagramTensor.{u, u, v} A).op

@[simp]
theorem diagramMappingTarget_obj (A W : C ⥤ SSet.{u}) :
    (diagramMappingTarget A).obj W = diagramMappingSpace.{u, u, v} A W := rfl

local instance diagramTensor_preservesColimits (A : C ⥤ SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (diagramTensor.{u, u, v} A) where
  preservesColimitsOfShape {J} := by
    intro _
    apply preservesColimitsOfShape_of_evaluation
    intro c
    change PreservesColimitsOfShape J (tensorLeft (A.obj c))
    infer_instance

private def diagramTensorIsLeftKanExtension (A : C ⥤ SSet.{u}) :
    (diagramTensor.{u, u, v} A).IsLeftKanExtension
      (𝟙 (SSet.stdSimplex.{u} ⋙ diagramTensor.{u, u, v} A)) := by
  letI : HasColimitsOfSize.{0, u} (C ⥤ SSet.{u}) :=
    hasColimitsOfSizeShrink.{0, u, u, u} _
  letI : PreservesColimitsOfSize.{0, u} (diagramTensor.{u, u, v} A) :=
    preservesColimitsOfSize_shrink.{u, 0, 0, u} _
  exact Presheaf.isLeftKanExtension_of_preservesColimits.{u, 0, u}
    (diagramTensor.{u, u, v} A) (Iso.refl _)

/-- The actual functor `K ↦ A × K` is left adjoint to the displayed simplicial
mapping space, with all naturality supplied by Mathlib's presheaf adjunction. -/
def diagramTensorMappingAdjunction (A : C ⥤ SSet.{u}) :
    diagramTensor.{u, u, v} A ⊣ diagramMappingTarget A := by
  letI := diagramTensorIsLeftKanExtension A
  letI : HasColimitsOfSize.{0, u} (C ⥤ SSet.{u}) :=
    hasColimitsOfSizeShrink.{0, u, u, u} _
  let adj : diagramTensor.{u, u, v} A ⊣
      Presheaf.restrictedULiftYoneda.{u} (SSet.stdSimplex.{u} ⋙ diagramTensor.{u, u, v} A) :=
    Presheaf.uliftYonedaAdjunction (diagramTensor.{u, u, v} A)
      (𝟙 (SSet.stdSimplex.{u} ⋙ diagramTensor.{u, u, v} A))
  let e := Functor.isoWhiskerRight (uliftYonedaIsoYoneda.{u} (C := C ⥤ SSet.{u}))
    ((Functor.whiskeringLeft _ _ _).obj (SSet.stdSimplex.{u} ⋙ diagramTensor.{u, u, v} A).op)
  exact adj.ofNatIsoRight e

end

end DaggerModels.PartII
