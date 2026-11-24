import DaggerModelsPartII.JTGraphParameterRelative
import DaggerModelsPartII.JTGraphInterpolatedRaw

/-!
# Relative time data in the fixed decorated target
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTNecklaceEndpointCylinder
open DaggerModels.PartII.JTGraphLiftTransport
open DaggerModels.PartII.JTCommaGraphPredecessor (augmentationCode)

namespace DaggerModels.PartII.JTGraphRelativeInterpolatedRaw

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {S : NecklaceCode}
variable (U : JTGraphFactoredPresentation.TargetComma Q)
variable (D : GraphLift U.left S)

/-- The decorated map retains prescribed parameter data on the time subobject. -/
theorem restricted_cylinder {A : SSet.{0}} {n : SimplexCategory}
    (j : A ⟶ J.obj n) (p : S.toSSet ⊗ A ⟶ J.obj (degree U.left))
    (q : S.toSSet ⊗ J.obj n ⟶ J.obj (degree U.left))
    (hq : (𝟙 S.toSSet ⊗ₘ j) ≫ q = p) :
    ((𝟙 S.toSSet ⊗ₘ j) ≫ (cylinder S).app n) ≫
        (JTGraphInterpolatedRaw.toDecoratedBy U D.collapse q).right =
      lift (fst S.toSSet A) p ≫ (cylinder S).app (degree U.left) := by
  change ((𝟙 S.toSSet ⊗ₘ j) ≫ (cylinder S).app n) ≫
      JTInterpolatedReducedCylinder.cylinderMap S q = _
  rw [Category.assoc, JTInterpolatedReducedCylinder.cylinderMap_cylinder,
    ← Category.assoc]
  have h : (𝟙 S.toSSet ⊗ₘ j) ≫
      lift (fst S.toSSet (J.obj n)) q =
      lift (fst S.toSSet A) p := by
    rw [← hq]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
    · simp only [Category.assoc, lift_snd]
  rw [h]

/-- An exact partial-time traversal extends to the actual fixed target,
including its complete raw comparison and exact restriction. -/
theorem exists_relative_decorated {A : SSet.{0}} {n : SimplexCategory}
    (j : A ⟶ J.obj n) [Mono j]
    (p : S.toSSet ⊗ A ⟶ J.obj (degree U.left))
    (hp : lift (fst S.toSSet A ≫ (D.collapse ≫ augmentationCode U.left).map) p ≫
        (cylinder (code U.left)).app (degree U.left) =
      fst S.toSSet A ≫ D.collapse.map ≫ U.left.fiber.hom.right) :
    ∃ q : S.toSSet ⊗ J.obj n ⟶ J.obj (degree U.left),
      (𝟙 S.toSSet ⊗ₘ j) ≫ q = p ∧
      (JTGraphInterpolatedRaw.toDecoratedBy U D.collapse q).right ≫
          ((DecoratedCylinderNecklacePresentation.underCocone W x y).app
            (JTGraphInterpolatedRaw.index U D.collapse)).right =
        NecklaceCylinderAugmentation.augmentation S n ≫
          (D.collapse ≫ U.hom.hom).map ≫ Q.map ∧
      ((𝟙 S.toSSet ⊗ₘ j) ≫ (cylinder S).app n) ≫
          (JTGraphInterpolatedRaw.toDecoratedBy U D.collapse q).right =
        lift (fst S.toSSet A) p ≫ (cylinder S).app (degree U.left) := by
  obtain ⟨q, hq, hfull⟩ := JTGraphParameterRelative.extend_time j
    (code U.left) (degree U.left) (D.collapse ≫ augmentationCode U.left).map
    (D.collapse.map ≫ U.left.fiber.hom.right) D.parameter D.comm p hp
  refine ⟨q, hq, ?_, restricted_cylinder U D j p q hq⟩
  exact JTGraphInterpolatedRaw.whole_raw_by U D.collapse q hfull

end

end DaggerModels.PartII.JTGraphRelativeInterpolatedRaw
