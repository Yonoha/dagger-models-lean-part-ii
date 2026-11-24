import DaggerModelsPartII.DiagramMappingSpace
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Limits of the strict mapping-space functor

For a fixed diagram `W`, strict simplicial mapping spaces turn colimits in
the source diagram into limits of simplicial sets.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite MonoidalCategory Simplicial

universe u v w t

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]

/-- Strict simplicial mapping space, contravariant in its diagram source. -/
def diagramMappingSource (W : C ⥤ SSet.{u}) :
    (C ⥤ SSet.{u})ᵒᵖ ⥤ SSet.{u} where
  obj A := diagramMappingSpace A.unop W
  map f := diagramMappingPrecomp f.unop W
  map_id A := by
    simp
  map_comp f g := by
    simp

@[simp] theorem diagramMappingSource_obj (W A : C ⥤ SSet.{u}) :
    (diagramMappingSource W).obj (op A) = diagramMappingSpace A W := rfl

@[simp] theorem diagramMappingSource_map (W : C ⥤ SSet.{u})
    {A B : C ⥤ SSet.{u}} (f : A ⟶ B) :
    (diagramMappingSource W).map f.op = diagramMappingPrecomp f W := rfl

private def tensorBySimplex (n : SimplexCategory) :
    (C ⥤ SSet.{u}) ⥤ (C ⥤ SSet.{u}) :=
  (Functor.whiskeringRight C SSet.{u} SSet.{u}).obj
    (tensorRight (SSet.stdSimplex.obj n))

/-- The strict mapping-space functor preserves every limit for which the
corresponding diagram colimit exists. -/
theorem diagramMappingSource_preservesLimitsOfShape
    (J : Type w) [Category.{t} J]
    [HasColimitsOfShape Jᵒᵖ SSet.{u}]
    [HasLimitsOfShape J ((C ⥤ SSet.{u})ᵒᵖ)]
    (W : C ⥤ SSet.{u}) :
    PreservesLimitsOfShape J (diagramMappingSource W) := by
  apply preservesLimitsOfShape_of_evaluation
  intro n
  let T := tensorBySimplex (C := C) n.unop
  letI : BraidedCategory SSet.{u} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfShape Jᵒᵖ
      (tensorLeft (SSet.stdSimplex.obj n.unop)) := inferInstance
  letI : PreservesColimitsOfShape Jᵒᵖ
      (tensorRight (SSet.stdSimplex.obj n.unop)) :=
    preservesColimitsOfShape_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (SSet.stdSimplex.obj n.unop))
  letI : PreservesColimitsOfShape Jᵒᵖ T := by
    dsimp [T, tensorBySimplex]
    infer_instance
  letI : PreservesLimitsOfShape J T.op := preservesLimitsOfShape_op J T
  letI : PreservesLimitsOfShape J (yoneda.obj W) := inferInstance
  change PreservesLimitsOfShape J (T.op ⋙ yoneda.obj W)
  infer_instance

end

end DaggerModels.PartII
