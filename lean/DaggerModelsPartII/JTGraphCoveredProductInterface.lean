import DaggerModelsPartII.JTJointRelativeParameters
import DaggerModelsPartII.JTVariableMiddleWhiskeredDiagram
import DaggerModelsPartII.JTParametrizedTargetFamilyComparison

/-!
Explicit product interfaces for covered evaluations.

`JTDecoratedIntervalDiagram.parameterize_map_left` identifies each sliced
parameter operator with the literal native/time tensor. Use this equation
before specializing to a large coefficient-choice family.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphCoveredProductInterface

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I]
variable (N : I ⥤ NecklaceCode) (time : I ⥤ SimplexCategory)

/-- The literal underlying native/time tensor, independent of its raw target. -/
abbrev product : I ⥤ SSet.{0} :=
  ((N ⋙ NecklaceCode.simplicialFunctor).prod' (time ⋙ J)) ⋙
    MonoidalCategory.tensor SSet.{0}

variable {X : SSet.{0}} (U : NecklaceCode)
variable (q : U.toSSet ⟶ X) (c : N ⟶ (Functor.const I).obj U)

/-- Forgetting the over-target frame gives the literal product, with
identity components and the exact original native/time operators. -/
def iso : product N time ≅
    JTJointRelativeParameters.withTime q J time (Over.lift N c)
      (JTTargetIntervalOverMapping.whole U) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro a b f
    change ((N.map f).map ⊗ₘ J.map (time.map f)) ≫ 𝟙 _ =
      𝟙 _ ≫ ((JTDecoratedIntervalDiagram.parameterize q J time
        (Over.lift N c ⋙ JTTargetIntervalOverMapping.whole U)).map f).left
    rw [Category.comp_id, Category.id_comp,
      JTDecoratedIntervalDiagram.parameterize_map_left]
    rfl)

theorem iso_hom_app (a : I) : (iso N time U q c).hom.app a = 𝟙 _ := rfl

section Degree

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)

variable {W : Source} {x y : Vertex W}
variable {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}

/-- The coefficient degree of a three-piece family is the supplied degree
diagram, without reducing its concrete coefficient data. -/
theorem degrees_labels
    (F : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y) P M R K) :
    JTParametrizedTargetFamilyComparison.degrees F.labels = K := rfl

end Degree
end
end DaggerModels.PartII.JTGraphCoveredProductInterface
